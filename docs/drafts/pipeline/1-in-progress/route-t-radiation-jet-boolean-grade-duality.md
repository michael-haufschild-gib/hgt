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

## 26. Conjecture loop 9 — bounded Cayley clock instead of exponential functional calculus

The continuous square flow is mathematically exact, but its Lean upper bound would require the
reverse exponential spectral-mapping theorem, which is absent from the current mathlib toolchain.
This is not a mathematical obstacle.  Apply a source-sized Cayley transform before iterating.

Put

```text
A = -i B^2,
h = 1 / (2(1+norm(A))),
X = h A,
U = (I+X)(I-X)^(-1).                                    (RJG54)
```

Here `h>0` and `norm(X)<1`, so `I-X` is unconditionally invertible by its Neumann series.  Every
object in (RJG54) is defined from the fixed theta density.  No zero, spectral projection, or RH
parameter enters the definition.

For every scalar `x`, the Cayley map

```text
kappa(x)=(1+x)/(1-x)
```

satisfies

```text
norm(kappa(x)) > 1  iff Re(x)>0,
norm(kappa(x)) = 1  iff Re(x)=0,
norm(kappa(x)) < 1  iff Re(x)<0,                           (RJG55)
```

whenever `norm(x)<1`.  This follows after squaring from the exact identity

```text
normSq(1+x)-normSq(1-x)=4 Re(x).
```

### Theorem K — exact source Cayley spectral map `[PAPER-PROVED]`

For every `k != -1`, multiplication on the right by the unit `I-X` gives

```text
(kI-U)(I-X)=(k-1)I-(k+1)X.
```

Consequently

```text
k in spectrum(U)
 iff (k-1)/(k+1) in spectrum(X),                          (RJG56)
```

and `-1` is not in `spectrum(U)`.  Thus (RJG56) is a full rational spectral-mapping theorem proved
by elementary unit algebra; no holomorphic-functional-calculus infrastructure is needed.

Since `B` is compact, the nonzero spectrum of `B^2` consists exactly of the squares of nonzero
eigenvalues of `B`.  The corpus identifies those eigenvalues with
`mu_q=-(alpha_q)^(-1)`.  Hence the nonessential Cayley multipliers are

```text
kappa_q = (1-i h mu_q^2)/(1+i h mu_q^2),                 (RJG57)
```

while the compact accumulation point `mu=0` maps to `kappa=1`.

### Theorem L — rank-two observed Cayley growth law `[PAPER-PROVED]`

Define the source-only discrete observation

```text
O_n = C U^n.                                              (RJG58)
```

For every canonical theta divisor mode, (RJG45), the unit inverse in (RJG54), and elementary
eigenvector calculus give

```text
U^n f_q = kappa_q^n f_q,
O_n f_q = kappa_q^n C f_q,
norm(O_n f_q)=norm(kappa_q)^n norm(C f_q),                (RJG59)
```

with `C f_q != 0`.  Under RH all `mu_q^2` are real, so (RJG55)--(RJG57) put the whole spectrum of
`U` on the unit circle and its spectral radius is one.  Gelfand's formula then makes
`norm(U^n)` subexponential.  Conversely, if RH fails, some reciprocal square is nonreal;
conjugation chooses a copy with positive imaginary part, so (RJG55) gives
`norm(kappa_q)>1`.  The lower bound obtained from (RJG59) then forbids subexponential growth of
`norm(O_n)`.

Therefore

```text
RH
 iff for every r>1,
       norm(C U^n)/r^n -> 0 as n->infinity.               (RJG60)
```

This is an unconditional equivalence of a classical statement with a fixed, bounded, source-built
two-channel discrete dynamical system.  It removes both the moving mass/cubic aperture and the
missing exponential spectral-mapping API.  Status: `[PAPER-PROVED] [NOVELTY UNVERIFIED]`.

## 27. Failed colligation shortcut and its positive survivor

### Conjecture

The same rank-two observer might be the adjoint defect `B+B^dagger`, making `U` an immediate
finite-rank conservative colligation.

### Verdict: `[FALSE FOR THIS B]`

The identity `V+V^dagger=C` holds for the bare pinned Volterra operator `V`.  The actual theta
source inverse has the weighted form

```text
B g(t)=i quantileSpeed(t) Vg(t),
```

and its Hilbert adjoint is the operator of the transposed weighted kernel.  The weights occur on
opposite variables, so they do not collapse to the unweighted rank-two `C`.  Treating `C` as
`B+B^dagger` would be theatre and would assert a false conservation law.

### Positive survivor

`C` remains a faithful finite observer by its exact nonzero monopole (RJG45), while `U` supplies
the full source evolution independently.  The correct architecture is therefore an observable
pair `(U,C)`, not a unitary colligation.  This distinction fixes where the remaining estimate must
live: in the two output channels, not in a nonexistent ambient energy conservation law.

## 28. Revised universal principle

The robust object is not a preferred time parameter.  It is a **source-defined functional model
plus a finite faithful observer**.  Any holomorphic map sending the stability boundary to a
geometric boundary yields the same obstruction provided it is regular on the whole source
spectrum.  The exponential sends the imaginary axis to zero continuous-time type; the Cayley map
sends it to the unit circle and turns type into spectral radius.  The scaled Cayley choice is
superior for formalization because invertibility is certified by `norm(X)<1` before any spectral
argument.

## 29. New Route T open core

Prove directly from the theta/von-Mangoldt source, before divisor decomposition,

```text
for every r>1, norm(C U^n)/r^n -> 0.                     (RJG61)
```

Because `C` has rank two, (RJG61) is exactly a pair of adjoint resolvent-orbit estimates for the
constant and centered-coordinate boundary vectors.  Neumann expansion of `(I-X)^(-1)` is
available unconditionally from `norm(X)<1`; cancellation must be proved across its iterated
source coefficients.  Assuming spectral radius at most one, reciprocal-square reality, RH, or
(RJG61) itself is circular.

## Log, Cayley receiver pivot

- 2026-08-10 — replaced the exponential API bottleneck by the scaled source Cayley clock; proved
  paper-level rational spectral mapping, exact rank-two modal growth, and RH equivalence (RJG60).
- 2026-08-10 — rejected the false shortcut `B+B^dagger=C`; retained the faithful observable-pair
  architecture and isolated the two-channel Neumann-orbit producer (RJG61).

## 30. Conjecture loop 10 — singular-metric Cayley Green identity

The failed ambient colligation conjecture used the wrong metric.  In quantile coordinates write

```text
V = pinnedVolterraCLM,
C = V^dagger+V,
q(t) = quantileSpeed(thetaSource,t),
G = M_(1/q),
B = i M_q V.                                             (RJG62)
```

`G` is the already constructed bounded, positive, injective theta metric with dense range.  Although
`M_q` is not a bounded operator, the products in the next identity are bounded.  Pointwise
cancellation of `q` gives

```text
G B = i V,
B^dagger G = -i V^dagger,
G B-B^dagger G = i C.                                   (RJG63)
```

Thus the correct source Green law is a **metric commutator**, not the false unweighted adjoint
defect from Section 27.  For `A=-iB^2`, (RJG63) telescopes once:

```text
G A+A^dagger G
 = -i (G B^2-(B^dagger)^2 G)
 = C B+B^dagger C.                                      (RJG64)
```

This is an exact rank-at-most-four source boundary defect.  It is stronger than the modal flux
law: it holds on the whole Hilbert space before any zero or eigenvector is selected.

Let `X=hA`, `R=(I-X)^(-1)`, and `U=(I+X)R` as in (RJG54).  Expanding the two Cayley squares and
using `(I-X)R=I` gives the discrete Green identity

```text
U^dagger G U-G
 = 2 h R^dagger (C B+B^dagger C) R.                     (RJG65)
```

Consequently, for every `n>=1`,

```text
(U^n)^dagger G U^n-G
 = 2 h sum_(j=0)^(n-1)
     (R U^j)^dagger (C B+B^dagger C) (R U^j).            (RJG66)
```

Equations (RJG63)--(RJG66) are `[PAPER-PROVED] [NOVELTY UNVERIFIED]`.  They identify the Cayley
clock as a conservative singular-metric evolution with all nonconservation confined to four
explicit boundary legs.  No RH information is used.

## 31. Hostile coercivity test and exact failure

### Conjecture

Use positivity of `G` and the finite-rank work term in (RJG66) to bound the ambient Cayley orbit.

### Verdict: `[FALSE IN EVERY FIXED FINITE-RANK AUGMENTATION]`

The theta metric symbol tends to zero at both interval endpoints.  Hence there is no `c>0` with

```text
<G f,f> >= c norm(f)^2.                                  (RJG67)
```

Adding any fixed finite family of bounded observations does not repair this.  Given bounded
functionals `ell_1,...,ell_m`, choose `m+1` disjoint normalized packets inside an endpoint interval
where `norm(G)` is arbitrarily small and take a nonzero linear combination in the kernel of all
`ell_j`.  After normalization it has every `ell_j(f)=0` and arbitrarily small `<Gf,f>`.  Therefore

```text
<G f,f> + sum_j |ell_j(f)|^2
```

is never equivalent to the ambient `L2` norm.  In particular the two channels of `C`, or even all
four legs in (RJG65), cannot turn `G` into a coercive conserved energy.  This rules out the entire
fixed-energy completion of the colligation idea, rather than merely one guessed identity.

### Positive survivor

The boundary defect is nevertheless exact and finite.  The producer must exploit that its vectors
are not arbitrary endpoint packets: they are the structured resolvent orbits `R U^j f`, and
`G B=iV` converts every occurrence of `B` into a bounded causal primitive.  The remaining estimate
must therefore be a propagation/cancellation theorem on this structured orbit, not an ambient
coercivity theorem.

## 32. Revised source producer after the Green identity

The source task (RJG61) admits a sharper pre-divisor form.  Prove that the accumulated boundary
work in (RJG66), evaluated on the two adjoint observation vectors spanning `range(C)`, grows
subexponentially.  After substituting `GB=iV`, every coefficient is an iterated pinned-Volterra
integral with positive theta weight and a rank-two affine endpoint contraction.  The exact target is

```text
for every r>1 and each e in {pinnedOne,pinnedCoordinate},
  norm((U^dagger)^n C e)/r^n -> 0.                       (RJG68)
```

This is equivalent to (RJG61) because `range(C)` is exactly the affine two-dimensional space.
Unlike a spectral-radius bound, (RJG68) names two fixed source vectors and can be attacked through
the Volterra kernel before divisor decomposition.  The next conjecture loop will test whether the
Neumann coefficients of `R` admit a factorial simplex gain after every boundary contraction; a
mere geometric norm bound is too weak and will be rejected.

## Log, singular-metric Green pivot

- 2026-08-10 — discovered the exact metric commutator `GB-B^dagger G=iC`, squared Green defect,
  Cayley metric-work identity, and its telescoping law (RJG63)--(RJG66).
- 2026-08-10 — proved the fixed finite-rank coercivity strategy impossible; isolated structured
  resolvent-orbit cancellation and the two adjoint boundary vectors as the surviving producer.

---

## 33. Conjecture loop 11 — factorial simplex gain after boundary contraction

### Conjecture

Use the Volterra factor in `G B=iV` to prove a uniform factorial estimate for the observed source
coefficients, for example

```text
norm(C X^k) <= K R^k/k!                                  (RJG69)
```

or the corresponding estimate on both adjoint seeds spanning `range(C)`.  Combined with the
coefficient expansion of `U^n=(I+X)^n(I-X)^(-n)`, such a bound would make the observed orbit grow
like `exp(O(sqrt(n)))` and close (RJG61).

### Verdict: `[FALSE — EVERY DIVISOR EIGENLINE SURVIVES THE CONTRACTION]`

Fix a divisor copy `q`, put `x_q=thetaXiBoundaryScaledEigenvalue(q)`, and
`f_q=thetaXiDivisorEigenvector(q)`.  The existing exact laws give

```text
X f_q=x_q f_q,
x_q != 0,
C f_q != 0.
```

Therefore, for every `k`,

```text
C X^k f_q=x_q^k C f_q,
norm(C X^k f_q)=norm(x_q)^k norm(C f_q).                 (RJG70)
```

If (RJG69) held, division by the nonzero fixed quantities would give

```text
k! <= constant * (R/norm(x_q))^k
```

for every `k`, contradicting the elementary fact that factorial eventually dominates every fixed
geometric sequence.  The same argument applies jointly to the two adjoint boundary seeds: since
`C f_q` is a nonzero vector in the affine two-dimensional range, at least one coordinate against
`C pinnedOne` and `C pinnedCoordinate` is nonzero.  Hence no fixed source basis can hide the modal
geometric coefficient behind factorial Volterra decay.

This is not merely failure of an operator-norm estimate.  It proves that multiplying by the
singular metric and exposing a bare Volterra primitive cannot be iterated coefficientwise: every
subsequent uncancelled `B` restores the full reciprocal-Xi eigenvalue.  Any proof which takes norms
between the Volterra factors has already lost the only possible cancellation.

### Positive survivor — cancellation must occur across Cayley orders

The binomial/negative-binomial coefficient of `X^k` in `U^n` cannot be bounded term by term.
Required estimate must retain the signed sum over `k` until after the rank-two contraction:

```text
C U^n
 = sum_(k>=0) [z^k]((1+z)/(1-z))^n * C X^k.             (RJG71)
```

On each divisor line this signed series sums exactly to `kappa(x_q)^n`; asking it to be
subexponential is exactly asking `Re(x_q)=0`.  Thus a generic Volterra-simplex theorem would be an
RH-equivalent spectral assertion in disguise.  The only noncircular successor is an arithmetic
identity coupling the coefficients `C X^k` before spectral decomposition — equivalently, a
centered prime--Gamma Ward identity for the whole generating function in (RJG71), not a bound for
its individual Taylor coefficients.

## 34. Big-picture synthesis after the failed simplex loop

The mass-light-cone, parabolic heat, and Cayley charts now display one universal obstruction:

```text
half-density arithmetic boundary
  -> signed prime--Gamma generating function
  -> holomorphic interior/divisor response
  -> finite faithful observation.                               (RJG72)
```

Maximum-principle bounds, fixed Hardy filters, finite-rank metric completion, and factorial
Volterra estimates all act before the signed boundary sum is completed.  Each therefore sees the
larger half-density boundary type and cannot control the interior response.  Poincare--Lelong,
parabolic heat, and the singular-metric Cayley law are three exact ways to move the observation,
but none changes this ordering.

The reasons for the repeated stalls are shadows of one higher principle:

> **Boundary-before-norm principle.**  For a faithful completed-Xi receiver, subcritical interior
> type can only be created by the exact signed prime--Gamma boundary relation.  Any positive,
> absolute, coefficientwise, or fixed-condition-number operation applied before that relation
> retains the enclosing boundary type.

This principle narrows the next Route T conjecture.  Do not estimate `C X^k`, `C U^n`, the bulk
Poincare--Lelong term, or individual prime channels.  Construct one coefficient-exact generating
identity equating (RJG71), after pairing with the two affine boundary vectors, to the centered
von-Mangoldt/Gamma current before norms.  Only then seek a Ward cancellation.  A proposed identity
must be checked against (RJG70): if it implies factorial or absolute decay on each divisor mode,
it is false.

## Log, coefficientwise no-go

- 2026-08-10 — falsified the factorial-simplex successor by exact observed divisor eigenlines;
  proved coefficientwise Volterra decay impossible and isolated across-order signed Cayley
  summation as the only surviving source mechanism.
- 2026-08-10 — unified mass-cone, heat, and Cayley failures under the boundary-before-norm
  principle; next viable theorem must be a coefficient-exact prime--Gamma Ward generating law.

---

## 35. Conjecture loop 12 — remove the reciprocal square before Cayley transformation

The square flow was inherited from the mass/heat coordinate `alpha^2`.  It is not intrinsic to the
fixed compact source inverse.  RH is already equivalent to reality of every nonzero eigenvalue of

```text
B=thetaKernelOperator,
mu_q=-(alpha_q)^(-1).
```

Choose

```text
h_1=1/(4(1+norm(B))),
X_1=i h_1 B,
U_1=(I+X_1)(I-X_1)^(-1).                              (RJG73)
```

Then `norm(X_1)<1`, so denominator is unconditionally a unit.  On a divisor line,

```text
x_q=i h_1 mu_q,
kappa_q=(1+x_q)/(1-x_q).                                (RJG74)
```

Since `Re(i mu_q)=-Im(mu_q)`, scalar Cayley geometry gives

```text
norm(kappa_q)=1  iff Im(mu_q)=0 iff Im(alpha_q)=0.       (RJG75)
```

Line conjugation sends `mu_q` to its complex conjugate, so every off-line pair supplies one
expanding multiplier.  The pinned monopole still gives `C f_q!=0`.  The compact-perturbation and
Gelfand proof of (RJG60) therefore applies verbatim and yields the strictly simpler receiver

```text
RH iff for every r>1, norm(C U_1^n)/r^n -> 0.            (RJG76)
```

Status: `[PAPER-PROVED] [NOVELTY UNVERIFIED]`.  No spectral mapping beyond compact Fredholm and the
elementary Cayley transport is used.

### Exact improvement of the Green law

The direct clock interacts with (RJG63) without the extra square.  Because `h_1` is real,

```text
G X_1+X_1^dagger G
 = i h_1(GB-B^dagger G)
 = -h_1 C.                                                (RJG77)
```

Let `R_1=(I-X_1)^(-1)`.  The Cayley expansion now gives

```text
U_1^dagger G U_1-G=-2h_1 R_1^dagger C R_1.              (RJG78)
```

This defect has rank two, not merely rank at most four.  Using the already formalized amplitudes

```text
<Cg,g>=|In(g)|^2-|Out(g)|^2,
```

and setting `g=R_1 f`, (RJG78) is exactly

```text
<G U_1 f,U_1 f> + 2h_1 |In(R_1 f)|^2
 = <G f,f> + 2h_1 |Out(R_1 f)|^2.                       (RJG79)
```

Thus the correct source object is a singular-state, one-in/one-out conservative scattering
system.  The earlier conclusion that no conservative colligation exists was specific to the
unweighted ambient metric and to the squared clock.  In canonical singular metric, direct clock
has an exact positive port balance.

### Hostile audit

Equation (RJG79) does not by itself prove (RJG76).  `G` remains noncoercive and autonomous source
orbits need not satisfy `In(R_1U_1^j f)=0`.  Summing (RJG79) merely trades state energy for signed
incoming/outgoing flux.  However, it removes two avoidable losses:

1. boundary work is exactly two-channel rather than four-leg;
2. no coefficientwise square or reciprocal-square functional calculus separates the two ports.

The new producer is now precise: prove source passivity of the direct scattering orbit,

```text
sum_(j<n)|Out(R_1U_1^j f)|^2
 <= sum_(j<n)|In(R_1U_1^j f)|^2 + exp(o(n)) norm(f)^2,   (RJG80)
```

on the two adjoint boundary seeds, by a coefficient-exact centered prime--Gamma identity.  Taking
absolute values portwise or replacing `G` by a fixed coercive completion is excluded by Sections
31 and 33.

### Positive source-resolvent chart

The denominator `I-X_1=I-i h_1B` is one source resolvent at the purely imaginary pencil parameter
`z=-i h_1`.  The ODE formula behind `thetaRealResolventMoment` extends to complex `z` only after an
endpoint audit.  For `g in L^2(0,1)`, its pinned primitive satisfies

```text
|h_g(t)| <= min(sqrt(t),sqrt(1-t)) ||g-pinnedMean(g)||_2.
```

The coarse unit-rate theta tail gives `t <= K exp(Q(t))` at the left endpoint and
`1-t <= K exp(-Q(t))` at the right endpoint.  Consequently

```text
sourceChar(z,Q(t)) h_g(t) -> 0 at both endpoints
```

whenever `|Im(z)|<1/2`.  Existing all-shift theta theorem upgrades this provisional bound to every
fixed complex `z`; Section 36 performs exact audit.  Integration of first-order resolvent equation
then yields

```text
pinnedMean((I+zB)^(-1)f)
 = [integral_0^1 sourceChar(z,Q(t)) f(t) dt]
   / rootA(thetaSource,z,1),                              (RJG81)

rootA(thetaSource,z,1)=XiC(z)/thetaSource.mass.
```

The factor `4` in (RJG73) leaves a uniform Neumann margin; no finite endpoint-strip restriction is
ultimately needed.  At `z=+-i h_1`, integrating factor is real exponential
`exp(-/+h_1 Q(t))`.  Hence direct Cayley ports have a coefficient-exact fixed safe-pencil
representation before divisor decomposition.
This is the concrete generating-law interface missing after (RJG71): powers of `U_1` become
repeated derivatives/finite differences of the two source resolvents in (RJG81), with literal
theta moments in numerator and completed Xi source in denominator.  Formalization must prove the
complex resolvent moment law rather than assume it from the real-parameter theorem.

## Log, direct-Cayley pivot

- 2026-08-10 — removed unnecessary reciprocal square; direct source Cayley clock gives same exact
  RH growth receiver with simpler spectral transport.
- 2026-08-10 — discovered exact rank-two singular-metric port balance (RJG79), upgrading the
  observable pair to a one-in/one-out conservative scattering system.
- 2026-08-10 — identified complex source-resolvent moment formula (RJG81) at two fixed imaginary
  safe-pencil points as the coefficient-exact prime--Gamma generating interface.

---

## 36. Conjecture loop 13 — complex resolvent endpoint audit

### Initial conjecture

Formula (RJG81) should follow for every complex `z` in the Neumann disk by copying the real
integrating-factor proof.

### Verdict: `[GENERICALLY FALSE AS STATED; TRUE FOR THETA AT EVERY COMPLEX PARAMETER]`

The algebraic ODE is unchanged, but the endpoint argument is not.  If

```text
E_z(t)=sourceChar(z,Q(t)),
h_g(t)=integral_0^t g-u*pinnedMean(g),
```

then the exact integrated equation contains the boundary term

```text
[E_z(t) h_g(t)]_(t=0)^(t=1).                            (RJG82)
```

For real `z`, `|E_z|=1` and this term vanishes from the pinned endpoints.  For nonreal `z`, the
factor grows at one quantile endpoint, so Neumann invertibility alone does not remove (RJG82).
This is a genuine logical gap in the initial version of (RJG81).

There is an exact generic repair.  Cauchy--Schwarz gives

```text
|h_g(t)| <= sqrt(t) ||g-m||_2,
|h_g(t)| <= sqrt(1-t) ||g-m||_2.                         (RJG83)
```

The coarse unit exponential tail and `cdf(Q(t))=t` give, near the two endpoints,

```text
t <= K exp(Q(t)),
1-t <= K exp(-Q(t)).                                    (RJG84)
```

Since `|E_z(t)|=exp(-Im(z)Q(t))`, (RJG83)--(RJG84) first imply

```text
E_z(t)h_g(t) -> 0 at 0 and 1 whenever |Im(z)|<1/2.      (RJG85)
```

This threshold is not sharp for theta.  Existing theorem `hasShiftedTail_thetaSource_all` proves
integrability after every real exponential tilt.  For fixed `z`, choose a tail rate strictly larger
than `2|Im(z)|`; same quantile-tail argument forces (RJG85) at both endpoints.  Thus theta has no
finite endpoint strip, and (RJG81) is paper-proved for every `z` for which source pencil is a unit.
Elementary Neumann sufficient condition is only

```text
|z| norm(B)<1.                                          (RJG86)
```

Direct step satisfies this strictly.  Initial `1/2` conclusion came from stopping at coarse source
envelope and was itself an incomplete corpus audit.  Surviving point is stronger: reusing real
theorem without proving boundary term false would be theatre, while all-shift corpus removes that
term for every fixed complex parameter.

### Positive survivor — two exact Esscher rows

At `z=-i h_1`, put

```text
E_-(t)=exp(h_1 Q(t)),  A=integral_0^1 E_-(t)dt,
R_-=(I-i h_1 B)^(-1).
```

Then `A=rootA(thetaSource,-i h_1,1)>0` and (RJG81) becomes the positive normalized row

```text
pinnedMean(R_- f)=integral_0^1 [E_-(t)/A] f(t)dt.        (RJG87)
```

Evenness of the theta source gives `Q(1-t)=-Q(t)`.  The opposite resolvent has
`E_+(t)=E_-(1-t)` and the same normalizer `A`.  Hence the two safe imaginary resolvents carry a
pair of reflected probability rows.  This positivity occurs before divisor decomposition and is
new source structure, not an RH restatement.

## 37. Conjecture loop 14 — does the positive mean row make the ports passive?

### Conjecture

Use (RJG87) to make both direct-Cayley port rows positive and deduce (RJG80) by Markov contraction.

### Exact two-port kernel

For `g=R_-f`, let `p=Vg`, `F(t)=integral_0^t E_-(u)f(u)du`, and
`A(t)=integral_0^t E_-(u)du`.  The Green formula is

```text
p(t)=E_-(t)^(-1) [F(t)-A(t)F(1)/A].                     (RJG88)
```

Since `pinnedCentered(g)=-integral_0^1 p(t)dt`, Fubini gives

```text
pinnedCentered(R_-f)=integral_0^1 E_-(u) psi(u) f(u)du,
psi(u)=J/A-integral_u^1 E_-(t)^(-1)dt,
J=integral_0^1 E_-(t)^(-1)A(t)dt.                       (RJG89)
```

Therefore the complete incoming/outgoing rows are

```text
In(R_-f)  = (1/sqrt(2)) integral E_-(u)[1/A-psi(u)]f(u)du,
Out(R_-f) = (1/sqrt(2)) integral E_-(u)[1/A+psi(u)]f(u)du. (RJG90)
```

The residual profile has the rigid first-order law

```text
psi'(u)=E_-(u)^(-1)>0,
integral_0^1 E_-(u)psi(u)du=0.                          (RJG91)
```

Thus all non-Markov behavior of the two-port resolvent is compressed into one strictly increasing,
single-crossing scalar profile.  At `h_1=0`, `psi(u)=u-1/2`, recovering the affine pinned ports.

### Verdict: `[MEAN-ROW ARGUMENT ALONE FALSE; SINGLE-CROSSING SURVIVES]`

Positivity of (RJG87) controls only `pinnedMean o R_-`.  Equation (RJG90) shows that port positivity
additionally requires the nontrivial sharp bound `|psi(u)|<=1/A`; it does not follow from Neumann
invertibility, endpoint decay, or the Markov normalization.  Moreover `U_1=2R_--I`, so even
one-step positivity would not by itself survive Cayley iteration.

The viable successor is narrower: exploit single crossing (RJG91), reflection of the opposite
tilt, and centered prime--Gamma variation to control signed products of the two port rows.  Any
claim that replaces `psi` by its absolute value destroys the reflection cancellation and violates
the boundary-before-norm principle.

## Log, endpoint and port-kernel pivot

- 2026-08-10 — found and repaired missing complex-resolvent endpoint term; proved the exact
  `|Im z|<1/2` L2 strip and changed direct step to lie strictly inside it.
- 2026-08-10 — discovered reflected Esscher probability rows (RJG87) at the two direct safe pencils.
- 2026-08-10 — derived full two-port Green kernel (RJG88)--(RJG91); rejected mean-only Markov
  passivity and isolated one monotone single-crossing profile as the remaining source obstruction.

---

## 38. Conjecture loop 15 — exploit theta reflection inside the single-crossing profile

Reflection collapses (RJG89) further.  Write `E=E_-` and keep `A(t)=integral_0^t E`.  Since

```text
E(1-t)=E(t)^(-1),
```

one has

```text
integral_u^1 E(t)^(-1)dt=A(1-u),
psi(u)=J/A-A(1-u),
J=integral_{u+v<=1} E(u)E(v)dudv.                       (RJG92)
```

Let `X,Y` be independent draws from normalized even theta source on the line.  Quantile change of
variables identifies

```text
A=E[exp(h_1 X)],
J=E[exp(h_1(X+Y)) 1_(X+Y<=0)],
A^2-J=E[exp(h_1(X+Y)) 1_(X+Y>0)].                       (RJG93)
```

The law of `X+Y` is symmetric.  Hence `J<=1/2` for every `h_1>0`.  Substitution into (RJG90) gives
the exact port-positivity classification

```text
the In row is strictly positive unconditionally,
the Out row is nonnegative iff A^2-J<=1.                (RJG94)
```

Indeed the In density is

```text
E(u)[(1-J)/A+A(1-u)]/sqrt(2)>0,
```

while the Out density is

```text
E(u)[(1+J)/A-A(1-u)]/sqrt(2),
```

whose minimum is at `u=0` and equals `(1+J-A^2)/A` up to the positive factor.

### Conjecture and verdict

Choose the safe Cayley step small enough that (RJG94) holds, then infer RH from positive ports.

Status: `[FIRST CLAUSE TRUE; INFERENCE FALSE]`.  At zero step, `A=1` and `J=1/2`, so
`A^2-J=1/2<1`.  Continuity supplies a fixed positive source-defined step satisfying simultaneously
the Neumann bound, endpoint strip, and both port-positivity inequalities.  Thus one-step two-port
positivity is unconditional source structure.

It still cannot imply RH: `U_1=2R_--I`, and every hypothetical off-line divisor mode has an
expanding multiplier for every positive step, however small.  Local positivity of the two rows
does not close their span under `U_1^dagger` and cannot control repeated signed extrapolation.

### Positive survivor — all-order tilted convolution is the real producer

Equations (RJG92)--(RJG94) replace an infinite-dimensional one-step sign problem by a one-sided
exponential moment of the symmetric convolution source.  The unresolved object is now its
all-order analogue generated by `(2R_--I)^n`: a signed binomial family of iterated Green kernels.
Required cancellation is not arbitrary operator cancellation; it is an all-order variation law
for reflected Esscher convolutions.  This is the first source-side formulation that simultaneously
retains positivity, reflection, and Cayley order without mentioning Xi zeros.

## Log, reflected-convolution reduction

- 2026-08-10 — collapsed single-crossing profile to triangular reflected Esscher integral.
- 2026-08-10 — proved incoming row positive and classified outgoing positivity by one scalar
  convolution moment; proved a sufficiently small positive safe step exists unconditionally.
- 2026-08-10 — falsified one-step port positivity as an RH producer; isolated all-order reflected
  Esscher convolution variation as next hard source statement.

---

## 39. Conjecture loop 16 — sum all Cayley orders before estimating

Put `K=qV=-iB`, so

```text
R_h=(I+hK)^(-1),
U_1=(I-hK)(I+hK)^(-1)=2R_h-I,
h=h_1.
```

For a formal orbit variable `w`, direct operator algebra gives

```text
(I-wU_1)^(-1)
 = 1/(1-w) (I+hK)(I+a(w)K)^(-1),
a(w)=h(1+w)/(1-w).                                     (RJG95)
```

Since

```text
I+hK = a(w)^(-1)h (I+a(w)K) + (1-a(w)^(-1)h)I,
```

the exact orbit generating row of any linear functional `L` is

```text
sum_(n>=0) w^n L(U_1^n f)
 = L(f)/(1+w)
   + [2w/(1-w^2)] L((I+a(w)K)^(-1)f).                  (RJG96)
```

For `L=pinnedMean`, (RJG81) turns this into

```text
sum_(n>=0) w^n pinnedMean(U_1^n f)
 = pinnedMean(f)/(1+w)
   + [2w/(1-w^2)]
       integral_0^1 exp(a(w)Q(t))f(t)dt
       / rootA(thetaSource,-i a(w),1).                  (RJG97)
```

Formula (RJG97) is the coefficient-exact generating identity demanded after (RJG71).  It sums all
signed Cayley orders before taking any norm, contains no divisor enumeration, and exposes literal
theta source in numerator and completed Xi source in denominator.  The centered and In/Out rows
have the same formula with the single-crossing kernel (RJG89) in place of the mean row.

Status: `[PAPER-PROVED] [NOVELTY UNVERIFIED]`.  This is strictly stronger than the two fixed safe
pencils: the entire orbit is one moving Esscher resolvent under Cayley--half-plane coordinate.

### Hostile audit — endpoint wall disappears, leaving genuine zero-freeness

All-shift theorem changes conclusion.  Every exponential theta tilt, its square, and one additional
quantile factor are integrable.  Hence

```text
a |-> exp(a Q(·))                                    (RJG98)
```

is an entire `L2(0,1)`-valued map.  Formula (RJG97) is therefore meromorphic wherever algebraic
moving resolvent is defined; no horodisk boundary comes from source integrability.

Moreover numerator vector `exp(aQ(·))` is never zero.  Every zero of

```text
A(a)=rootA(thetaSource,-i a,1)
```

is a genuine pole of mean-row generating function; no scalar numerator cancellation can hide it.
Under `a=h(1+w)/(1-w)`, RH becomes exactly zero-freeness of this normalized bilateral Laplace
transform on right half-plane, equivalently analyticity of `L2` row on unit disk:

```text
RH <=> A(a)!=0 for Re(a)>0
   <=> row in (RJG97) is analytic for |w|<1.             (RJG99)
```

This removes one apparent obstacle rather than renaming it: theta decay is already strong enough,
and remaining obstruction is purely zero geometry of an entire positive-source Laplace transform.
Next producer must exploit structure stronger than positivity and all exponential moments--for
example total positivity, convolution factorization, or a prime--Gamma variation law forcing
right-half-plane zero-freeness.  Generic endpoint estimates are now proved irrelevant.

## Log, all-order resolvent summation

- 2026-08-10 — summed direct Cayley orbit exactly into one moving source resolvent (RJG95)--(RJG97).
- 2026-08-10 — used existing all-shift theorem to remove provisional endpoint horodisk; reduced
  remaining problem to genuine right-half-plane zero-freeness of entire positive-source Laplace
  transform, detected faithfully by an `L2`-valued Cayley row.

---

## 40. Conjecture loop 17 — is the moving mean row complete or only faithful on named modes?

Define normalized Esscher row, away from zeros of `A`, by

```text
v_a(t)=exp(aQ(t))/A(a).
```

All-shift theta theorem implies `a |-> exp(aQ(·))` is entire as an `L2(0,1)`-valued map: square
integrability uses tilt `2 Re(a)`, and local differentiation is dominated by one additional
exponential tilt.  Its Gram kernel is exact:

```text
<v_a,v_b>=A(conj(a)+b)/(conj(A(a))A(b)).                (RJG100)
```

At any positive safe `h`, derivatives have triangular form

```text
D^n v_a|_(a=h)
 = exp(hQ)/A(h) * [Q^n + polynomial of degree < n].     (RJG101)
```

### Density theorem

Existing `EntireExponentialMomentPolynomialDensity.lean` says polynomials are dense in `L2` of any
finite measure with all bilateral exponential moments.  Apply it to theta law tilted by
`exp(2hQ)`.  Multiplication by `exp(hQ)` transports its polynomial core to ordinary quantile space.
Therefore

```text
closure span {D^n v_h : n>=0}=L2(0,1).                 (RJG102)
```

This is paper-proved without RH, zero simplicity, divisor completeness, or computation.

### Direct-clock cyclicity

In (RJG97), `a(w)=h(1+w)/(1-w)` has `a(0)=h` and `a'(0)=2h!=0`.  Coefficient comparison is
triangular: zeroth orbit row is pinned mean, first gives `v_h`, and coefficient `n+1` contains a
nonzero multiple of `D^n v_h` plus earlier derivatives.  Consequently

```text
closure span {(U_1^dagger)^n pinnedOne : n>=0}=L2(0,1). (RJG103)
```

Status: `[PAPER-PROVED] [NOVELTY UNVERIFIED]`.  Direct Cayley receiver is not merely nonzero on
canonical divisor modes: one scalar boundary row is cyclic for full adjoint clock.  Every invariant
subspace is exposed by its all-order source orbit.  This also explains why multiplicity copies do
not defeat observation: source ODE supplies one geometric eigenline while algebraic multiplicity
can remain in its Jordan chain.

### Hostile audit

Cyclicity closes observability, not orientation.  A cyclic compact perturbation can still have
off-axis eigenvalues, and (RJG103) makes any proposed positive form more demanding because its sign
must extend from a dense polynomial core.  Route-U corpus already proves generic moment positivity,
PF2/log-concavity, and total-positivity shortcuts insufficient or circular at adaptive contact.

Positive survivor is exact: combine dense cyclic core with rank-two Green identity before cumulant
compression.  If a nonnegative source form controls direct orbit on all weighted quantile
polynomials, density upgrades it to whole state space; if it vanishes on one cyclic source vector,
existing dense-radical no-go forces nonclosability unless arithmetic prime--Gamma term supplies
orientation.  Thus missing producer cannot be another finite observer.  It must be a closable
source-specific form orienting adaptive prime--Gamma shear on dense cyclic core.

## Log, direct-clock cyclicity

- 2026-08-10 — proved moving Esscher row is entire `L2`-valued and has exact Gram kernel.
- 2026-08-10 — transported existing entire-moment polynomial density to weighted quantile jets.
- 2026-08-10 — derived unconditional cyclicity of pinned mean for adjoint direct Cayley clock;
  eliminated hidden-subspace/finite-observer explanations of Route T obstruction.

---

## 41. Conjecture loop 18 — determinant-weighted resolvent-frame energy

### Conjecture

Use the now-dense adjoint resolvent frame to synthesize a positive whole-space form.  If its
determinant weight retains enough of the moving divisor, positivity plus cyclicity might orient the
direct clock.

### Exact source--Fourier bridge

For `u` in the reciprocal-density source space, put

```text
z(h,tau)=-tau-i h,
p_(h,u)(x)=exp(hx)u(x)/sqrt(M).
```

The all-complex source-character moment satisfies the pointwise identity

```text
Moment(z(h,tau),Uu)=Fourier(p_(h,u))(tau/(2*pi)).       (RJG104)
```

Hence, whenever the tilted profile lies in `L1 intersect L2`, Plancherel gives

```text
integral_R |Moment(z(h,tau),Uu)|^2 d tau
  =2*pi integral_R |p_(h,u)(x)|^2 dx.                 (RJG105)
```

At zero tilt every source vector satisfies the required `L1 intersect L2` conditions.  The `L2`
claim is not an extra domain premise: boundedness of the theta density makes ordinary Lebesgue
`L2` weaker than the defining reciprocal-density norm.  Therefore

```text
integral_R |Moment(z(0,tau),Uu)|^2 d tau
  =2*pi <G Uu,Uu>,                                    (RJG106)
```

where `G` is the canonical singular metric.

The law is fully polarized.  For arbitrary source vectors `u,v`,

```text
integral_R conj(Moment(z(0,tau),Uu)) Moment(z(0,tau),Uv) d tau
 =2*pi integral_R conj(p_(0,u)(x)) p_(0,v)(x) dx.      (RJG107)
```

Thus off-diagonal complex Gram data does not retain hidden zero orientation.

### Exterior resolvent cancellation

On every exterior line `|h|>=1/2`, every pencil is unconditionally invertible and

```text
pinnedMean(R_z Uu)=Moment(z,Uu)/A(z).
```

Consequently the determinant weight cancels the divisor pointwise:

```text
|A(z)|^2 |pinnedMean(R_z Uu)|^2=|Moment(z,Uu)|^2,      (RJG108)
```

and, before any absolute value or diagonalization,

```text
|A(z)|^2 conj(pinnedMean(R_z Uu)) pinnedMean(R_z Uv)
 =conj(Moment(z,Uu)) Moment(z,Uv).                     (RJG109)
```

### Verdict: `[FAILED AS PRODUCER — FULL POLARIZED NO-GO; POSITIVE SURVIVOR FORMALIZED]`

The obstruction is stronger than failure of one energy estimate.  Every determinant-weighted
quadratic or sesquilinear synthesis of this complete resolvent row cancels the scalar Xi divisor
before Plancherel and lands on physical source pairing.  Cyclicity supplies complete observation,
but determinant weighting followed by Gram formation is an information-loss functor from divisor
phase to source metric.

Lean status: `[FORMALIZED] [COMPILES]` in
`HedenmalmThetaResolventMetricPlancherel.lean`; the exterior adjoint-resolvent frame is formalized
in `HedenmalmThetaEsscherResolventFrame.lean` and the exact fixed-line Gram/cyclicity law in
`HedenmalmThetaEsscherCyclicity.lean`.

## 42. Higher universal principle and revised Route T producer

Repeated failures now have one common explanation:

```text
source phase --divide by A--> resolvent row
             --multiply by |A|^2 and polarize--> source metric.
```

Positive completion, determinant packaging, and even full complex polarization all apply the
second arrow.  They cannot orient a zero because they algebraically remove the divisor that needs
orientation.  This is why finite ports, dense cyclic observers, positive Green completions, and
metric-frame synthesis keep producing strong receivers without moving the centered-prime frontier.

The next admissible producer must remain phase-linear before determinant weighting.  The canonical
candidate is the normalized first Esscher jet

```text
(partial_a A(a))/A(a)=partial_a log A(a),              (RJG110)
```

or its centered version, read as one unsquared resolvent row.  Unlike (RJG108)--(RJG109), it keeps
oriented poles with multiplicity.  Route T's continued centered von Mangoldt--Gamma current already
lands on this logarithmic derivative, so (RJG110) is the first exact interface between the dense
source receiver and the unresolved timelike-plus-glancing prime flux.

New open core: derive a source-side phase law for the unsquared normalized jet that controls the
cofinal `Lambda-1` pairing before norms, Gram formation, or reflection aggregation.  Any proposal
that first multiplies by `A`, `conj(A)`, `|A|^2`, or takes a norm is now ruled out by
(RJG108)--(RJG109), not merely suspected to be lossy.

## Log, resolvent-frame Plancherel pivot

- 2026-08-11 — formalized exact all-complex moment/Fourier bridge and its `2*pi` Plancherel law.
- 2026-08-11 — proved every reciprocal theta-source vector is ordinary Lebesgue `L2` and identified
  critical moment energy exactly with canonical singular metric.
- 2026-08-11 — proved full polarized cross-pairing law; closed off-diagonal Gram loophole.
- 2026-08-11 — proved pointwise exterior determinant cancellation for diagonal and complex
  cross-Gram resolvent rows; retired determinant-weighted frame synthesis as Route T producer.

---

## 43. Conjecture loop 19 — quantile log-jet as phase-linear prime receiver

### Conjecture

The first quantile coordinate, rather than a positive completion of the full source frame, should
extract the normalized first Xi jet before determinant cancellation.  This would give a canonical
unsquared receiver for Route T's continued centered prime--Gamma current.

Let `Q` be the theta-source quantile coordinate, viewed in `L2(0,1)`.  Its square integrability is
unconditional because the theta source has finite second moment.  Differentiating the exact
quantile characteristic representation of `XiC` and using source evenness gives, for every complex
`z`,

```text
Moment(z,Q)=-i XiC'(z)/M.                              (RJG111)
```

At every invertible pencil point, the exact scalar resolvent row therefore is

```text
pinnedMean(R_z Q)=-i XiC'(z)/XiC(z)
                 =-i logDeriv(XiC)(z).                (RJG112)
```

Unlike (RJG108)--(RJG109), (RJG112) is linear in phase and retains every divisor pole with its
algebraic multiplicity.  No norm, conjugation, Gram formation, or determinant weighting occurs.

On the fixed exterior line `z=-tau-i`, invertibility and zeta nonvanishing are unconditional.
The existing prime--Gamma continuation theorem then identifies the same receiver with the exact
Route T source trace:

```text
pinnedMean(R_(-tau-i) Q)
  =-i continuedPrimeArchSourceRelativeTrace(-tau-i).  (RJG113)
```

Verdict: `[PROVED — PHASE-SENSITIVE SOURCE/ARITHMETIC INTERFACE]`.

Lean status: `[FORMALIZED] [COMPILES]` in
`HedenmalmThetaResolventLogJet.lean`.

### Hostile audit

(RJG113) is an exact safe-line boundary identity, not a zero-free continuation theorem.  Resolvent
analyticity cannot be carried through an unknown pole, and the formal identity deliberately assumes
invertibility away from the exterior line.  Thus this result does not prove RH and does not move the
centered `Lambda-1` cancellation frontier by itself.

Positive survivor is nevertheless stronger than every previous receiver: Route T's arithmetic
current is now literally one cyclic theta-resolvent matrix coefficient, with full complex phase and
pole multiplicity intact.  The remaining producer problem has a precise operator form: transport
the unsquared row from the safe exterior line toward the critical line using a cancellation law that
is proved before norms and remains meaningful at a first hypothetical pole.

## Log, quantile log-jet pivot

- 2026-08-11 — formalized unconditional `L2` membership of theta quantile coordinate.
- 2026-08-11 — proved exact all-complex first-jet moment formula (RJG111).
- 2026-08-11 — proved exact phase-linear resolvent/logarithmic-derivative identity (RJG112).
- 2026-08-11 — welded fixed safe-line receiver to continued prime--Gamma trace (RJG113).

---

## 44. Conjecture loop 20 — coherent exterior-row realization of the mass current

### Conjecture

Do not transport one safe resolvent value through the unknown strip.  Instead place the entire
legal Euler bottom line inside Route T's analytic mass packet.  The prime--Gamma split may then
turn the complete mass current into one coherent superposition of phase-linear theta rows while
remaining wholly inside the unconditionally invertible exterior resolvent set.

For `c>1/2`, real `x`, and

```text
z_(c,x)=x-i c,
s_(c,x)=1/2+c+i x=1/2+i z_(c,x),
```

the quantile log-jet and safe Euler source identity give the pointwise law

```text
L(Lambda)(s_(c,x))
 =logDeriv(archFactor)(s_(c,x))
  -pinnedMean(R_(z_(c,x)) Q).                           (RJG114)
```

Every pencil in (RJG114) is unconditionally invertible.  Multiplying before integration by Route
T's analytic mass bottom test and retaining complex phase gives

```text
MassPrime(a,c,tau)
 =MassArch(a,c,tau)
  -integral_R MassTest(a,c,tau,x)
      pinnedMean(R_(x-i c) Q) dx.                       (RJG115)
```

The archimedean term has an existing height-independent bound.  Consequently, for every legal
`1/2<c<a` and `sigma>0`,

```text
RH iff sup_(u>=0) |
  integral_R MassTest(a,c,sigma+i u,x)
    pinnedMean(R_(x-i c) Q) dx| < infinity.             (RJG116)
```

Verdict: `[PROVED — EXACT PHASE-LINEAR ROUTE-T/THETA WELD]`.

Lean status: `[FORMALIZED] [COMPILES]` in
`HedenmalmThetaXiMassPhaseLinearWeld.lean`.

### New structural knowledge

Route T obstruction is not failure to control individual safe-line resolvents: every row in
(RJG116) lies on one fixed zero-free exterior line.  Obstruction is coherent mass modulation of
the whole row family.  Taking norms rowwise destroys precisely the `u`-dependent cancellation.
Thus safe-line continuation and finite prime cutoff are both inessential representations; same
open core is a source-fixed operator wave packet.

### Hostile audit

(RJG116) is still a receiver criterion.  Generic resolvent bounds combined with absolute
integration inherit exponential `u` growth from the shifted mass test.  Any proof that estimates
rows separately, applies Cauchy--Schwarz before the `x` integration, or assumes an anti-Herglotz
sign merely recreates the already retired square-root loss or an RH-equivalent positivity
condition.  Admissible next step must use the resolvent identity and rank-two Green law coherently
under the mass integral, before norms.

## Log, coherent exterior-row pivot

- 2026-08-11 — proved pointwise Euler/Gamma/theta-resolvent split (RJG114).
- 2026-08-11 — proved complete integrated mass-current weld (RJG115).
- 2026-08-11 — isolated exact pure-theta exterior-wave-packet RH criterion (RJG116).

---

## 45. Conjecture loop 21 — lightlike quantile source and polarized Green current

### Conjecture

Use the rank-two Green law coherently before norms.  The quantile source might have exceptional
boundary orientation allowing the phase-sensitive monopole row to be recovered from flux.

### Exact source geometry

Let `Q` be the theta quantile coordinate and put

```text
d = pinnedFirstMoment(Q).
```

Evenness and strict quantile monotonicity prove, unconditionally,

```text
pinnedMean(Q)=0,
Re(d)>0,
pinnedIn(Q)=-pinnedOut(Q) != 0,
<C Q,Q>=0,
C Q=-d pinnedOne != 0.                                  (RJG117)
```

Thus `Q` is not in the boundary kernel.  It is a genuinely nonzero lightlike state of the
mixed-inertia rank-two form.  Quadratic Green energy is exactly blind to the canonical source.

The apparent no-go has a phase-linear polarization.  For every quantile-space state `g`,

```text
<C Q,g>=-d pinnedMean(g),                                (RJG118)
```

and the polarized metric commutator gives

```text
d pinnedMean(g)
 =-i( <G B Q,g> - <G Q,B g> ).                          (RJG119)
```

For every invertible theta pencil, `g=R_z Q` and the log-jet law therefore yield

```text
d logDeriv(XiC)(z)
 = <G B Q,R_z Q> - <G Q,B R_z Q>.                       (RJG120)
```

This is an exact fixed-source symplectic representation of the oriented Xi divisor current.  It
uses neither determinant weighting nor a quadratic form.

### Route T mass weld

On every legal exterior line `c>1/2`, define the coherent polarized current packet by integrating
the right side of (RJG120) against the analytic mass test, retaining the difference as one
integrand.  Then

```text
PolarizedPacket(a,c,tau)
 = i d ThetaResolventPacket(a,c,tau),                   (RJG121)
```

and for `1/2<c<a`, `sigma>0`,

```text
RH iff sup_(u>=0) |PolarizedPacket(a,c,sigma+i u)|<infinity. (RJG122)
```

Verdict: `[PROVED — PHASE-LINEAR GREEN POLARIZATION; PRODUCER BOUND STILL OPEN]`.

Lean status: `[FORMALIZED] [COMPILES]` in
`HedenmalmThetaQuantileBoundaryNull.lean`,
`HedenmalmThetaQuantileResolventPortLaw.lean`, and
`HedenmalmThetaXiMassPolarizedGreenWeld.lean`.

### Hostile audit and higher principle

Quadratic Green failure was not merely mixed inertia.  Canonical arithmetic source itself lies on
the boundary light cone, and desired monopole is symmetric port sum while energy sees difference
of port intensities.  Correct observable is cross flux with fixed lightlike source.

Polarization repairs information loss but does not yet prove boundedness: (RJG120) is exactly
`d logDeriv(XiC)`.  Splitting its two metric terms and estimating separately would destroy the
commutator cancellation and recreate the retired norm barrier.  Next admissible producer must
assemble the full `H`-valued exterior response packet and apply inverse-pencil equation or an exact
transport primitive to the combined symplectic current before any norm.

## Log, polarized Green pivot

- 2026-08-11 — proved quantile source has strictly positive dipole but zero quadratic boundary
  flux: a nonzero lightlike state.
- 2026-08-11 — proved cross boundary current extracts the phase-sensitive monopole exactly.
- 2026-08-11 — proved all-complex polarized metric representation of `logDeriv XiC`.
- 2026-08-11 — welded complete Route T mass packet to one coherent polarized Green current and
  isolated its exact RH line-bound criterion.

---

## 46. Conjecture loop 22 — divisor-wide affine interpolation by a rank-two source port

### Conjecture

The lightlike source `Q` may still control every divisor direction after quadratic energy loses it.
Test the two fixed source-built metric probes

```text
u = G Q,
v = G B Q
```

directly on each multiplicity-exact Xi divisor eigenvector `f_q`.

### Exact interpolation law

Every divisor mode has the same nonzero monopole:

```text
pinnedMean(f_q)=sqrt(M),                                 (RJG123)
```

where `M=thetaSource.mass`.  Since `B f_q=mu_q f_q`, the polarized Green law becomes the affine
interpolation identity

```text
<v,f_q>-mu_q <u,f_q>=i d sqrt(M),                       (RJG124)
```

with `d=pinnedFirstMoment(Q)` and `Re(d)>0`.  Right side is independent of `q`, nonzero, and retains
complex phase.

Source port is genuinely two-dimensional.  For every scalar `c`,

```text
B Q != c Q,
G B Q != c G Q.                                         (RJG125)
```

Zero-eigenvalue case of first assertion follows from injectivity of pinned primitive on centered
hyperplane.  Nonzero-eigenvalue case follows from exact theorem that every nonzero eigenvector of
`B` has nonzero monopole, whereas `Q` has zero monopole.  Second assertion follows from injectivity
of singular metric `G`.

Consequently no Xi divisor mode is dark to both fixed probes:

```text
not (<u,f_q>=0 and <v,f_q>=0).                           (RJG126)
```

Verdict: `[PROVED — UNCONDITIONAL DIVISOR-WIDE RANK-TWO OBSERVABILITY]`.

Lean status: `[FORMALIZED] [COMPILES]` in
`HedenmalmThetaDivisorPolarizedInterpolation.lean`.

### Hostile audit

(RJG126) is qualitative observability, not uniform coercivity.  It supplies no lower bound on
`max(|<u,f_q>|,|<v,f_q>|)` after normalization, and `G` is proved not bounded below.  Compactness
allows observed amplitudes to approach zero along high modes while affine compensation in
`mu_q<u,f_q>` remains exact.  Any argument replacing (RJG124) by separate absolute-value bounds
again destroys its cancellation and returns to the receiver barrier.

This closes the naive finite-frame conjecture.  Positive survivor is sharper: all divisor modes lie
on one fixed affine hyperplane in the two-probe/eigenvalue incidence space.  Missing producer is
therefore not visibility but a source-side uniform control of this affine incidence under the
coherent mass modulation.

### Failed pivots and higher principle

- A second scalar compensator cannot repair FCRJ: exact checkpoint is invariant under arbitrary
  linear stopped compensators.
- Hilbert cofinal meets collapse to zero; radial codiagonals saturate; common-carrier squares remain
  indefinite.
- Normalized resolvent profiles are exponentially unstable on mass-packet wings.
- Divisor boundary-flux positivity is precisely transverse-zero sign and hence RH-equivalent.
- Fixed integration by parts only yields polynomial decay against an exponential wing; all-order
  contour transport crosses exactly the unknown off-line poles.
- Fixed phase-natural source-faithful coefficient transport is identity; arbitrary positive
  transport exists only when the target RH scalar is already nonnegative.

Unified obstruction: arithmetic FCRJ defect and theta Green current are two realizations of a
noncommuting completion/trace curvature.  Scalar or radial completion kills its phase, while norm
completion loses coherent cancellation.  Live successor must be connection-valued and preserve the
full affine current before taking terminal trace; merely enlarging a scalar receiver is circular.

## Log, divisor interpolation pivot

- 2026-08-11 — proved exact constant monopole for every multiplicity-exact theta divisor mode.
- 2026-08-11 — proved fixed affine two-probe interpolation law (RJG124).
- 2026-08-11 — proved source port is genuinely nonproportional before and after the singular metric.
- 2026-08-11 — proved no Xi divisor mode is jointly dark to the two fixed probes.
- 2026-08-11 — rejected qualitative observability as a substitute for uniform mass-packet control.

---

## 47. Conjecture loop 23 — monopole rigidity of the full nonzero point spectrum

### Conjecture

The theorem that every nonzero `B`-eigenvector has nonzero monopole may force more than
observability: it should rigidify each nonzero eigenspace itself.

### Geometric simplicity theorem

Let `B=thetaCompactSourceInverse`.  If `c != 0`, `Bf=cf`, `Bg=cg`, and `g != 0`, then

```text
f = (pinnedMean(f)/pinnedMean(g)) g.                     (RJG127)
```

Indeed the displayed difference is a `c`-eigenvector with zero monopole.  If nonzero it
contradicts the exact eigenmonopole theorem.  Therefore every nonzero point eigenspace of `B` is
geometrically one-dimensional.

For every Xi divisor copy `q`, the canonical mode has monopole `sqrt(M)`, hence every vector in its
eigenspace is reconstructed from one scalar:

```text
Bf=mu_q f
  implies
f=(pinnedMean(f)/sqrt(M)) f_q.                           (RJG128)
```

In particular the mean-normalized divisor eigenvector is unique:

```text
Bf=mu_q f and pinnedMean(f)=sqrt(M) implies f=f_q.       (RJG129)
```

Verdict: `[PROVED — ALL NONZERO POINT EIGENSPACES ARE CANONICAL LINES]`.

Lean status: `[FORMALIZED] [COMPILES]` in
`HedenmalmThetaDivisorPolarizedInterpolation.lean`.

### Hostile audit

Geometric simplicity is not algebraic simplicity.  A Jordan chain at `mu_q` is equivalent to
higher Xi multiplicity through the Fredholm characteristic function; excluding it would prove the
open simplicity conjecture for Xi zeros and cannot be inferred from (RJG127).  Thus no semisimple
spectral expansion or orthogonal eigenbasis may be used downstream.

Positive survivor changes correct state space for the producer.  Divisor-location freedom is
one-dimensional at each point; all unresolved multiplicity is longitudinal jet data in the
generalized eigenspace.  Connection-valued aperture evolution must therefore act on Jordan jets,
not on an artificial family of independent eigenvectors at the same divisor point.

## Log, monopole-rigidity pivot

- 2026-08-11 — proved proportionality of arbitrary same-eigenvalue nonzero source-inverse modes.
- 2026-08-11 — proved exact reconstruction of every Xi eigenspace vector from its monopole.
- 2026-08-11 — separated geometric simplicity from open algebraic simplicity/Jordan-chain control.

---

## 48. Conjecture loop 24 — extinction of prime-path terminal flux

### Conjecture

The scalar valuation-one source may be the terminal holonomy of the ordered adjacent-prime path.
Finite Abel summation gives such a terminal term, but does not decide whether it survives at
infinity.  If it vanishes, the full source must instead be carried by a distributed
connection-gradient current.

### Sharp cumulative-mass law

Let

```text
A_(N+1)=sum_(n<=N) log(p_n)/sqrt(p_n).
```

The first `N+1` prime atoms inject into full von-Mangoldt mass through `p_N`.  The corpus sharp
Chebyshev-scale law therefore gives

```text
||A_(N+1)|| <= primeMassHalf(p_N) <= 21 sqrt(p_N).       (RJG130)
```

This removes logarithmic loss.  For any legal interior shift `1/2<d<a`, deep-strip Fourier decay
then gives

```text
||F(log p_N) A_(N+1)||
  <= 21 J_sigma exp(|u|d) exp(-(d-1/2) log p_N),         (RJG131)
```

and right side tends to zero since ordered primes are cofinal.  Thus terminal prime-path flux
vanishes unconditionally for every fixed vertical height.

### Exact ordered connection reconstruction

Define edge current

```text
C_n(a,tau)=A_(n+1) (F_tau(log p_n)-F_tau(log p_(n+1))).
```

Finite Abel identity becomes

```text
sum_(n<=N) primeAtom_n = F_tau(log p_N) A_(N+1) + sum_(n<N) C_n.  (RJG132)
```

The source series is absolutely summable for fixed `tau` with positive real part, while first term
vanishes by (RJG131).  Therefore ordered graph prefixes satisfy

```text
lim_(N->infinity) sum_(n<N) C_n
  = xiMassValuationOnePrimeLayer(a,tau).                 (RJG133)
```

Order is intrinsic.  (RJG133) is an ordered improper limit, not an unordered `tsum`; no absolute
summability of `C_n` is asserted.  Lean rejected that stronger inference and forced this distinction.

Consequently, for every `a>1/2` and `sigma>0`,

```text
RH iff sup_u ||lim_N sum_(n<N) C_n(a,sigma+iu)|| < infinity.  (RJG134)
```

Verdict: `[PROVED — TERMINAL FLUX EXTINCT; FULL SOURCE IS ORDERED CONNECTION CURRENT]`.

Lean status: `[FORMALIZED] [COMPILES]` in
`XiMassFullAdjacentPrimeConnection.lean`.

### Hostile audit

(RJG133) is not by itself a bound: pointwise equality with the original valuation-one layer would
be a renaming if terminal extinction were omitted.  New content is exact removal of boundary at
infinity using sharp square-root mass, plus localization of every surviving source contribution to
cumulative-mass-weighted graph gradients.  Taking absolute values of those gradients is not known
to be uniformly summable and would recreate the receiver barrier.

Higher principle: Route T obstruction is not scalar mass escaping at prime infinity.  Terminal
holonomy is zero.  Obstruction is distributed noncommutative transport along prime-log connection;
the scalar source appears only after ordered path integration.  Next producer must control coherent
connection current before terminal trace, likely by a curvature or square law coupling adjacent
prime transport to theta/Jordan jet connection.  Any proof based on a terminal boundary charge or
unordered norm sum is now ruled out.

## Log, prime-path connection pivot

- 2026-08-11 — proved sharp cumulative first-prime mass bound by full von-Mangoldt mass.
- 2026-08-11 — proved unconditional extinction of adjacent-prime terminal flux.
- 2026-08-11 — proved ordered connection-gradient prefixes converge to full valuation-one source.
- 2026-08-11 — proved RH equivalent to vertical boundedness of exact ordered connection current.
- 2026-08-11 — rejected unordered `tsum` claim; convergence order is essential source structure.

---

## 49. Conjecture loop 25 — exact Klein--Gordon propagation of the Xi mass profile

### Conjecture

The analytic Xi mass test should be a literal free Klein--Gordon orbit, including enough Bochner
derivative calculus to move the PDE through its Fourier integral.  If propagation itself supplied
the missing estimate, its conserved energy might control Route T.

### Exact specialization

For radial frequency

```text
omega_a(x)=sqrt(x^2+a^2),
```

all polynomial radial moments of the damped Xi mass integrand are integrable.  Differentiation
under the integral gives the full temporal moment tower, the exact mass-shell second-moment law,
and therefore

```text
partial_u^2 F_a(u,h)-partial_h^2 F_a(u,h)+a^2 F_a(u,h)=0.  (RJG135)
```

No weak derivative or distributional placeholder remains in (RJG135): both second derivatives are
the actual Bochner derivatives of the concrete mass profile.

Verdict: `[PROVED — EXACT PROPAGATION; REJECTED AS PRODUCER]`.

Lean status: `[FORMALIZED] [COMPILES]` in `XiMassKleinGordonConnection.lean`.

### Hostile novelty audit

Corpus C42-I already identified Klein--Gordon energy conservation and proved why it fails at the
source observation map.  Thus (RJG135) is valuable formal closure of the exact Xi specialization,
not new evidence for an RH bound.  The missing theorem is still continuity of the arithmetic
observation on the actual cyclic orbit; assuming that continuity would assume the open core.

The half-density gauge `G=e^(h/2)F` obeys the drifted equation

```text
G_uu-G_hh+G_h+(a^2-1/4)G=0.                              (RJG136)
```

but C43-L already proves its outgoing factor `1/2-partial_h` is the exact inverse of harmonic-tail
smoothing.  Consequently (RJG136) is a recoding of critical radiation, not a coercive gap.

## Log, Klein--Gordon audit

- 2026-08-11 — closed concrete Xi mass PDE with genuine Bochner second derivatives.
- 2026-08-11 — rejected ordinary or half-density Klein--Gordon energy as source producer by C42-I/L.

---

## 50. Conjecture loop 26 — critical half-density conditioning of the prime connection

### Conjecture

Square-root cumulative mass in (RJG130) may be a coordinate artifact rather than intrinsic
connection curvature.  Move the critical half-density from each prime coefficient into the mass
profile before Abel summation.

### Exact gauge and Mertens-scale connection

Put `h_n=log p_n` and

```text
b_n=log(p_n)/p_n,
G_tau(h_n)=e^(h_n/2)F_tau(h_n).
```

Then every literal source atom is preserved before summation:

```text
b_n G_tau(h_n)=(log p_n/sqrt p_n)F_tau(h_n).             (RJG137)
```

The cumulative connection coordinate now satisfies the unconditional Mertens bound

```text
||sum_(n<=N)b_n|| <= log p_N + K_M,                       (RJG138)
```

with an explicit corpus constant `K_M`.  For every legal interior depth `1/2<d<a`,

```text
||G_(sigma+iu)(h_N) sum_(n<=N)b_n||
 <= J_sigma e^(|u|d)(h_N+K_M)e^(-(d-1/2)h_N) -> 0.       (RJG139)
```

Hence the valuation-one source is exactly the ordered harmonic connection current

```text
lim_N sum_(n<N) (sum_(j<=n)b_j)(G_tau(h_n)-G_tau(h_(n+1))), (RJG140)
```

and boundedness of (RJG140) on one positive vertical line is equivalent to RH.

Verdict: `[PROVED — CONNECTION MASS CONDITIONED; CRITICAL RADIATION SURVIVES]`.

Lean status: `[FORMALIZED] [COMPILES]` in
`XiMassHalfDensityAdjacentPrimeConnection.lean`.

### Hostile novelty audit and higher principle

(RJG137)--(RJG140) prove square-root cumulative growth in the ungauged connection is not
intrinsic: exact half-density gauge reduces it to logarithmic growth and still kills terminal
flux.  Therefore neither prime infinity nor cumulative connection mass is Route T's obstruction.

This does not provide smoothing.  Corpus C43-J--L already shows harmonic primitive and mass
outgoing differential are exact inverse resolvents at every log-frequency.  Half-density profile
inherits precisely the critical radiation removed from the coefficient.  Taking total variation
of (RJG140) restores critical type.  New invariant separation is:

```text
terminal holonomy = 0;
cumulative-mass exponent = gauge-dependent;
ordered phase curvature = gauge-invariant open core.      (RJG141)
```

Live successor must compare this ordered prime curvature directly with the phase-linear theta
Green curvature before either is scalarized or normed.

## Log, half-density connection pivot

- 2026-08-11 — proved exact atomwise half-density gauge and explicit Mertens cumulative bound.
- 2026-08-11 — proved unconditional terminal extinction and ordered connection reconstruction.
- 2026-08-11 — isolated ordered phase curvature, not mass growth, as gauge-invariant obstruction.

---

## 51. Conjecture loop 27 — prime-connection / theta-Green anomaly compensation

### Conjecture

The ordered half-density prime connection and polarized theta Green current may be two gauges of
one anomaly.  Add them before taking norms and test whether valuation-one source cancels exactly.

### Exact Ward identity

Let `M_theta` be the pinned theta first moment, `G_theta(tau)` the polarized quantile Green packet,
and `C_prime(tau)` the half-density ordered prime connection.  Then

```text
G_theta(tau)+i M_theta C_prime(tau)
 = i M_theta [A_arch(tau)-(P_square(tau)+P_high(tau))].    (RJG142)
```

The right side is uniformly bounded on every positive vertical line.  Thus the two RH-strength
currents represent one common anomaly modulo the bounded ideal; any unbounded component is exactly
phase-antialigned before scalarization.

Verdict: `[PROVED — EXACT CROSS-ROUTE COMPENSATION]`.

Lean status: `[FORMALIZED] [COMPILES]` in
`HedenmalmThetaXiMassConnectionGreenCompensation.lean`.

### Hostile novelty audit

(RJG142) is stronger than two independent boundedness comparisons: it is an exact phase-linear Ward
identity.  It is not RH.  The identity cancels the valuation-one open core between two
representatives and therefore cannot bound either representative separately.  Successor question:
classify the entire bounded quotient rather than calling it harmless.

## Log, anomaly compensation

- 2026-08-11 — proved exact theta-Green / ordered-prime cancellation.
- 2026-08-11 — isolated one common quotient class modulo bounded background.

---

## 52. Conjecture loop 28 — timelike mass-shell Riemann--Lebesgue theorem

### Conjecture

Every integrable centered Xi mass-shell packet should vanish in future vertical time even though
the phase `sqrt(x^2+a^2)` is nonlinear and stationary-phase infrastructure was absent from Lean.

### Exact positive-energy pushforward

For `a>0`, put

```text
q_a(y)=sqrt(y^2-a^2),
D_(a,f)(y)=1_(a,infinity)(y) y/q_a(y) [f(q_a(y))+f(-q_a(y))].
```

The threshold singularity is integrable whenever `f` is integrable, and exact change of variables
gives

```text
integral_R e^(-iu sqrt(x^2+a^2)) f(x) dx
 = integral_R e^(-iuy) D_(a,f)(y) dy -> 0.                (RJG143)
```

Consequently every fixed Xi centered prime atom tends to zero vertically.

Verdict: `[PROVED — FULL TIMELIKE DISPERSION]`.

Lean status: `[FORMALIZED] [COMPILES]` in
`XiMassRadialRiemannLebesgue.lean`; one-sided zero-free contour transport is in
`StripHorizontalShift.lean`.

### Hostile novelty audit

This is not generic stationary-phase rhetoric: Lean proves the exact two-sheet pushforward,
Jacobian, image, injectivity, integrability, Fourier identity, and limit.  It removes the continuous
mass shell as a possible Route T obstruction.  It cannot be passed naively through the prime-square
series because its critical envelope is `sum_p log(p)/p`, which diverges.  Attempting dominated
convergence there would be false proof theatre and was rejected.

## Log, timelike dispersion

- 2026-08-11 — proved exact positive-energy threshold density and its integrability.
- 2026-08-11 — proved radial Riemann--Lebesgue extinction and fixed-atom extinction.
- 2026-08-11 — identified nonsummable prime-square boundary as sole failed interchange.

---

## 53. Conjecture loop 29 — residue spectrum of the compensated current

### Conjecture

The bounded quotient in (RJG142) may have a finite persistent carrier.  Classify it exactly rather
than estimating it.  Prime-square nonsummability should be a contour-crossing residue, not failure
of mass-shell dispersion.

### Prime-square pole and two-carrier classification

One-sided transport remains entirely in `Re s>=1`, so it uses the unconditional zeta zero-free
boundary and never enters the critical strip.  The square channel decomposes exactly as

```text
P_square(tau)
 = (pi/2) Phi_tau(0) + R_reg(tau)-R_high(tau),            (RJG144)
```

where both remainders tend to zero vertically.  The higher correction is reindexed exactly as the
absolutely summable even-prime-power tail `p^(2(k+2))`; no analytic continuation of its series is
assumed.

The centered archimedean packet and all high prime powers also tend to zero.  Therefore

```text
G_theta(sigma+iu)+i M_theta C_prime(sigma+iu)
 - i M_theta [2pi Phi_(sigma+iu)(-i/2)
              -(pi/2) Phi_(sigma+iu)(0)] -> 0.            (RJG145)
```

The surviving frequencies are exactly

```text
omega_arch=sqrt(a^2-1/4),   omega_square=a.               (RJG146)
```

Verdict: `[PROVED — COMPLETE TWO-RESIDUE ASYMPTOTIC CARRIER]`.

Lean status: `[FORMALIZED] [COMPILES]` in
`XiMassPrimeSquareAsymptoticCarrier.lean` and
`HedenmalmThetaXiMassCompensatedAsymptoticCarrier.lean`.

### Hostile novelty audit and higher universal principle

(RJG144)--(RJG146) create new source classification: every continuous-spectrum and absolutely
summable arithmetic component disperses; persistent vertical modes are exactly contour-crossing
residues.  The earlier bounded-quotient description hid this finite residue spectrum.

This still does not prove RH.  Valuation-one ordered phase curvature canceled in (RJG142), so
(RJG145) classifies the quotient but gives no separate bound for theta Green or prime connection.
The big-picture principle is now sharper:

```text
continuous mass shell       -> dispersive zero;
absolutely summable powers  -> dispersive zero;
crossed source divisors     -> finite residue spectrum;
valuation-one phase order   -> only remaining RH-strength degree of freedom. (RJG147)
```

Any successor route that acts only on the bounded quotient, mass shell, or repeated prime powers is
closed.  Progress must produce a phase-sensitive constraint on valuation-one order before its exact
theta/prime cancellation.

## Log, residue-spectrum pivot

- 2026-08-11 — proved square pole plus decaying regular and even-prime-power pieces.
- 2026-08-11 — proved centered arch and high-prime-power extinction.
- 2026-08-11 — proved full compensated current converges modulo two explicit residue carriers.
- 2026-08-11 — isolated valuation-one ordered phase as sole non-dispersive, non-residue open core.

---

## 54. Conjecture loop 30 — adaptive mass source/receiver phase wall

### Conjecture

A growing but sublinear mass aperture might damp the valuation-one source while retaining an
off-critical divisor boost.  Determine the exact faithful scale before attempting any source
estimate.

### Sharp faithfulness classification

For one Xi divisor copy `q`, write `R+iJ` for its Poisson point and `M_a+iK_a` for its mass image.
Charge conservation and the universal height bounds give

```text
M_a |K_a| = R |J|,       a <= M_a <= a+R.                (RJG148)
```

Consequently, for every aperture schedule `a_n>=1/2` and every off-line copy `J!=0`,

```text
n |K_(a_n)| -> infinity
  iff n/M_(a_n) -> infinity
  iff n/a_n -> infinity.                                 (RJG149)
```

The second equivalence is the new sharp half.  Its reverse direction uses
`M_(a_n)<=a_n+R<=(1+2R)a_n`; its forward direction uses `a_n<=M_(a_n)`.

Every unconditional oblique absorber has a positive linear velocity `v` with
`v*n<=a_n` eventually (and source phase chamber `4*sigma*v>1`).  Such a schedule cannot satisfy
`n/a_n->infinity`.  Hence

```text
oblique source extinction chamber  intersection
off-line faithful receiver chamber = empty.              (RJG150)
```

Verdict: `[PROVED — SHARP ADAPTIVE SOURCE/RECEIVER WALL]`.

Lean status: `[FORMALIZED] [COMPILES]` in
`XiMassAdaptiveApertureSharpFaithfulnessWall.lean`.

### Hostile novelty audit and pivot

(RJG149) is stronger than the earlier necessary sublinear condition: it classifies every adaptive
schedule exactly and is independent of which off-line Xi copy is selected.  (RJG150) kills the
remaining purely kinematic aperture hope.  No choice of mass graph can use the corpus's
unconditional oblique extinction estimate and simultaneously retain divergent off-line signal.

This does not rule out phase cancellation inside a faithful sublinear cone; proving that
cancellation remains the RH-strength arithmetic problem.  The positive survivor from the earlier
co-moving no-go is now forced: progress must be transverse to the aperture graph.  First mass
rescaling recovers the conserved signed charge `RJ` at `O(1/a)`, while the paper-proved
mass--Bessel obstruction excludes every finite radiation-jet subtraction.  Therefore the next
producer must be an infinite-jet, phase-linear aperture current, not another scalar mass schedule.

## Log, sharp adaptive wall

- 2026-08-11 — proved raised height is at most aperture plus fixed original height.
- 2026-08-11 — proved off-line boost divergence iff time/aperture ratio diverges.
- 2026-08-11 — proved faithful schedules and unconditional oblique absorbers are disjoint.
- 2026-08-11 — retired kinematic sublinear aperture as an RH closure mechanism.

---

## 55. Conjecture loop 31 — transverse parabolic mass face

### Corpus collision and surviving conjecture

Rest-energy renormalization suggests the parabolic face

```text
exp(2 a^2 t) exp(-2 a t sqrt(a^2+z^2))
  = exp(-2 a t (sqrt(a^2+z^2)-a))
  -> exp(-t z^2).                                        (RJG151)
```

This is not new paper mathematics: `mass-xi-finite-true-prime-cone.md`, especially its
C43-R--C43-V chain, already proves the exact remainder identity, divisor domination, heat-Hankel
bridge, and Euler-line Gaussian transfer.  Lean corpus does not yet contain the full-divisor
transfer.  Rebranding the limit as a discovery would be theatre.

The live conjecture is therefore formal and quantitative: construct the parabolic mass trace over
every Xi divisor copy, prove a uniform summable majorant, and prove unconditional convergence of
the complete multiplicity-exact `tsum` to the Gaussian Xi heat trace.  The algebraic core is

```text
2 a (beta-a) = z^2 - z^4/(beta+a)^2,
beta = sqrt(a^2+z^2),                                   (RJG152)
```

with a divisor-uniform positive-time majorant obtained from the mass height equation, not from
finite truncation or computation.

Status: `[IN PROGRESS — LEAN-DEFERRED PAPER THEOREM SELECTED FOR CLOSURE]`.

### Hostile audit and required pivot

Even complete formalization of (RJG151) does not prove RH: every linear chart currently known
(vertical mass, parabolic heat, theta resolvent, Cauchy/Hurwitz) transports the same signed
reflection defect instead of forcing it to vanish.  Value comes from removing the possibility that
the transverse limit hides an analytic gap and from exposing which nonlinear source laws survive
both mass and heat charts.  After the transfer theorem closes, next conjecture must constrain
valuation-one orientation nonlinearly; another linear smoothing identity is not progress.

## Log, transverse parabolic face

- 2026-08-11 — identified existing complete paper proof and refused duplicate novelty claim.
- 2026-08-11 — selected full multiplicity-exact mass-to-heat `tsum` convergence as missing Lean gap.

### Closure

The conjecture is now formalized.  Lean proves (RJG152), the `O(a^-2)` divisorwise error, the sharp
uniform gap `a(M_a-a)>=R/4`, domination by `xiPoissonWeight(t/2)`, and unconditional convergence
of the complete multiplicity-exact parabolic mass trace to the Gaussian Xi heat trace.

Verdict: `[PROVED ON PAPER BEFORE THIS LOOP; LEAN GAP NOW CLOSED]`.

Lean status: `[FORMALIZED] [COMPILES]` in `XiMassParabolicHeatTransfer.lean`.

---

## 56. Conjecture loop 32 — Stieltjes--Cassini orientation midpoint

### Conjecture

The parabolic heat chart and shifted-Cassini chart may retain complementary nonlinear halves of
the same orientation loss.  For one squared Xi coordinate `w=A+iB` and a fixed shift `y>0`, put

```text
lambda=(y+w)^(-1),
E=1/(y+A),
V=Re(lambda^2)/Re(lambda).                              (RJG153)
```

Direct algebra predicts the exact midpoint law

```text
E-Re(lambda)=Re(lambda)-V
  =B^2/((y+A)((y+A)^2+B^2)) >= 0.                       (RJG154)
```

Thus Route T's Hermitian heat envelope and Route U's Cassini intrinsic velocity should be
symmetric around the phase-linear shifted resolvent response.  Summing (RJG154) over the complete
Xi divisor is legal because every term is bounded by `1/(y+A)`, hence by the reciprocal-square
majorant.  The summed gap should vanish exactly under RH.

### Anti-theatre audit

Corpus contains the parabolic heat--resolvent Gamma bridge and the orbitwise Cassini phase-tax
threshold, but repository search found no theorem identifying their phase taxes as the same
Stieltjes midpoint gap or compressing it to one multiplicity-exact scalar.  This remains a receiver,
not annihilation.  Value is a new cross-route invariant: two apparently different nonlinear
obstructions are one positive density, so separate T/U source estimates would duplicate the same
open core.

### Closure

The conjecture is exact.  For every positive shift, Lean proves the orbitwise midpoint law,
summability of all three complete traces, and

```text
E_total-V_total=2 D_y,
D_y=sum_q B_q^2/((y+A_q)((y+A_q)^2+B_q^2)) >= 0.        (RJG155)
```

Moreover

```text
D_y=0
 iff E_total=Re M_y(0)
 iff E_total=V_total
 iff RH.                                                 (RJG156)
```

Since `V_total<=E_total` unconditionally, the reverse weak order `E_total<=V_total` is already an
exact one-scalar RH criterion.  This is a receiver theorem, not source annihilation.

The common atom has intrinsic Fisher form

```text
B_q^2/((y+A_q)((y+A_q)^2+B_q^2))
  = Im(lambda_q)^2/Re(lambda_q).                          (RJG157)
```

Hostile collision audit: Suzuki's pre-existing shifted transverse charge is not (RJG157); it is
the cubic density `|lambda_q|^2 Im(lambda_q)^2/Re(lambda_q)`.  The new midpoint density is its
radially normalized degree-one form.

Verdict: `[PROVED — EXACT STIELTJES--CASSINI MIDPOINT DEFECT]`.

Lean status: `[FORMALIZED] [COMPILES]` in
`XiHeatCassiniStieltjesOrientationDefect.lean`.

---

## 57. Conjecture loop 33 — valuation-one BV--Wold Fisher landing

### Conjecture

The valuation-one Wold source is not `ell^1` off the critical line, but its centered coefficient
is `ell^2`.  Let

```text
c_q(p)=primeDepthBVWoldXiRelativeLogCoefficient(q,1,p)-woldRemainder(p)
      =a_q woldCoeff(1,p),
a_q=2 Re(rho_q)-1,
C_W=sum_p woldCoeff(1,p)^2.                              (RJG158)
```

Then `0<C_W<infinity` and

```text
sum_p c_q(p)^2=a_q^2 C_W.                                (RJG159)
```

The shifted-imaginary coordinate formula predicts a strictly positive geometric gauge `G_y(q)`
with

```text
Im(lambda_q)^2/Re(lambda_q)=a_q^2 G_y(q),                (RJG160)
```

and hence the complete source/receiver conservation law

```text
C_W D_y=sum_q G_y(q) sum_p c_q(p)^2.                     (RJG161)
```

This would identify Route T's parabolic/Stieltjes defect as an honest positively weighted Hilbert
energy of the actual centered valuation-one source, not a divisor-only receiver.

### Hostile audit and expected wall

The law cannot itself prove RH: it transports, rather than annihilates, the horizontal source
rate.  Its value is sharper typing.  Existing polynomial Hilbert-charge flow with probe `X`
produces

```text
|lambda_q|^2 Im(lambda_q)^2/Re(lambda_q),                (RJG162)
```

so recovering (RJG157) requires division by `|lambda_q|^2`, equivalently the orbit-normalized
phase probe `lambda_q/|lambda_q|`.  That normalization is non-holomorphic and divisor-adaptive.
Thus fixed polynomial source probes necessarily land one radial degree too high.  If (RJG161)
closes, next conjecture must seek a source-native projective/unitary normalization or prove that
every such normalization is necessarily target-adaptive.

### Closure and sharp maximality wall

The conjecture is exact.  Lean proves `0<C_W<infinity`, (RJG159)--(RJG161), atomwise positivity of
`G_y`, and the complete source-energy landing without changing divisor multiplicity.  The existing
Suzuki/Hankel transverse charge is also proved to equal `|lambda_q|^2` times the midpoint density;
the degree mismatch is literal, not heuristic.

There is a stronger obstruction than non-holomorphic normalization.  Schwarz conjugation preserves
`a_q` and hence the entire centered Wold coefficient vector `p |-> c_q(p)`, while it reverses
`Im(lambda_q)`.  Therefore no function of that complete vector alone can recover the phase-linear
shifted orientation at an off-line copy.  The valuation-one Wold source is a maximal quadratic
receiver but cannot be a phase-linear producer.

Verdict: `[PROVED — EXACT FISHER LANDING AND SCHWARZ-PARITY MAXIMALITY NO-GO]`.

Lean status: `[FORMALIZED] [COMPILES]` in
`XiHeatCassiniBVWoldFisherLanding.lean`.

---

## 58. Conjecture loop 34 — phase-clock and reflected mixed-source jet

### Conjecture

The orientation density may retain a phase-linear source coordinate before its Fisher square.  For
one squared node `A+iB`, direct Laplace algebra predicts

```text
D_y(q)=integral_(0,infinity)
  exp(-(y+A)u) (1-cos(Bu)) du.                           (RJG163)
```

The corpus factorization `B=-(2 Re(rho)-1) Im(rho)` says this clock frequency is the product of
centered horizontal Wold grade `a` and physical height `gamma`.  The independent pre-divisor
phase/half-grade source should expose that product as a genuine mixed jet.

### Closure

Both statements are exact.  Lean proves integrability, nonnegativity, (RJG163), complete `tsum`
equality with `D_y`, and the resulting RH zero-energy criterion.  On continuous log-prime scale
`x`, reflection-minus-identity has imaginary source boundary

```text
J_(a,gamma)(x)=2 sinh(a x/2) sin(gamma x).               (RJG164)
```

It specializes exactly at `x=log p` to the existing reflected physical prime moment.  Its neutral
jets are

```text
J(0)=J'(0)=0,   J''(0)=2 a gamma=-2B.                   (RJG165)
```

Thus the Cassini clock is exactly driven by minus one half of a pre-divisor mixed source jet.  The
jet is odd under grade reflection, odd under Schwarz phase reversal, and even under their product:
it is the tensor-product sign representation lost by every separately completed quadratic source.

Lean status: `[FORMALIZED] [COMPILES]` in
`XiHeatCassiniPhaseClockLanding.lean` and
`XiHeatCassiniReflectedPhaseSourceJet.lean`.

### Hostile audit and pivot

(RJG164)--(RJG165) close source provenance, not source annihilation.  Continuous interpolation near
`x=0` has no unconditional arithmetic law forcing its curvature to vanish; treating analyticity
alone as such a law would be theatre.  The exact two-prime reflected Hermiticity specialization is
already RH-equivalent.  Therefore no further receiver normalization, Wold energy, or local source
jet can close Route T.

The surviving producer question returns to the actual open core: valuation-one ordered phase
curvature in the finite timelike/glancing mass cone.  New useful constraint is representation
theoretic: any proposed producer must retain the bi-odd grade--height tensor before Schwarz orbit
completion and before taking norms.  Phase-even or grade-even source completions are now ruled out
by theorem, not preference.

Verdict: `[PROVED — EXACT MIXED SOURCE-JET IDENTIFICATION; RETIRED AS ANNIHILATOR]`.

---

## 59. Conjecture loop 35 — raw Cassini/Wold compact-smoothing wall

### Conjecture and failure

The Fisher landing suggested that the depth-one Wold coefficient might directly control the raw
Route-T valuation-one critical coefficient.  Put

```text
r(p)=log(p)/sqrt(p),
c_1(p)=(1-1/p)^3 log(p)/p,
kappa(p)=(1-1/p)^3/sqrt(p).                              (RJG166)
```

The exact relation is

```text
c_1(p)=kappa(p) r(p),    0<kappa(p),    kappa(p)->0.      (RJG167)
```

Thus the conjectured coercive landing is false.  Lean proves

```text
sum_p r(p)^2=infinity,       sum_p c_1(p)^2<infinity,     (RJG168)
```

and there is no `c>0` with `c r(p)<=c_1(p)` at every prime.  Cassini Fisher energy is a compact
diagonal image of the ungauged critical source and cannot recover it by a bounded inverse.

### Positive survivor and pivot

This no-go exposed that the comparison had been made before Route T's canonical half-density
gauge.  The vanishing factor in (RJG167) contains exactly the `p^(-1/2)` moved from arithmetic
coefficient into mass profile by `XiMassHalfDensityAdjacentPrimeConnection.lean`.  Therefore the
correct next conjecture is not another inverse estimate on `r`; it is to compare Wold and Route T
after the half-density conjugation.

Verdict: `[PROVED — RAW COMPACT-SMOOTHING WALL; POSITIVE GAUGE SURVIVOR EXTRACTED]`.

Lean status: `[FORMALIZED] [COMPILES]` in
`XiHeatCassiniMassCriticalSmoothingWall.lean`.

---

## 60. Conjecture loop 36 — bounded Wold coframe and trace reduction

### Conjecture

After moving `sqrt(p)` into the mass test, Route T's arithmetic coefficient becomes

```text
h(p)=log(p)/p.
```

The depth-one Wold coefficient should then be uniformly coframe-equivalent rather than compactly
smoothed, and the difference should be harmless after restoring the half-density:

```text
c_1(p)=(1-1/p)^3 h(p),
1 <= (1-1/p)^(-3) <= 8,                                 (RJG169)
0 <= h(p)-c_1(p) <= 3 log(p)/p^2.                       (RJG170)
```

Multiplication of (RJG170) by `sqrt(p)` predicts the raw correction
`O(log(p)/p^(3/2))`, summable against the prime-uniform vertical mass Fourier bound.

### Closure

All predictions are exact.  Lean proves the bounded inverse coframe (RJG169), the positive
summable Euler depletion (RJG170), and the atomwise source decomposition

```text
critical Route-T atom(p)
  = sqrt(p)c_1(p) F_u(log p) + correction(p,u),           (RJG171)

|correction(p,u)|
  <= 3 log(p) p^(-3/2) integral_R exp(-sigma|x|) dx.      (RJG172)
```

The majorant is independent of vertical time `u`.  Consequently, with multiplicity and the full
cofinal prime sum preserved,

```text
L_T(a,sigma+iu)=L_W(a,sigma+iu)+R(a,sigma+iu),
sup_u |R(a,sigma+iu)| < infinity,                        (RJG173)

RH iff sup_u |L_W(a,sigma+iu)| < infinity,               (RJG174)
```

where `L_W` is the pure depth-one Wold coefficient paired with the physical Route-T mass
half-density profile.  This is stronger than a classifier rephrasing: it removes the full mismatch
between Cassini/Wold arithmetic data and the Route-T critical source modulo an explicitly
trace-class, uniformly bounded current.

Lean status: `[FORMALIZED] [COMPILES]` in
`XiHeatCassiniHalfDensityWoldCoframe.lean` and
`XiHeatCassiniWoldHalfDensityTraceReduction.lean`.

### Hostile audit and next pivot

(RJG174) does not bound `L_W`.  The fixed Wold coefficient is square summable, but the restored
half-density profile has timelike radiation; Cauchy--Schwarz on profile norms would again erase the
phase and can grow.  Fisher energy controls arithmetic coframe, not propagated test orbit.

The surviving open core is now sharper: prove a phase-linear bound for one positive depth-one Wold
logarithmic measure under the non-normal mass half-wave.  Mertens gives bounded discrepancy of the
underlying harmonic log-prime measure from Lebesgue measure, and (RJG170) changes that measure only
by finite positive mass.  Next conjecture must exploit this centered Wold discrepancy inside the
ordered joint pairing before total variation or Hilbert norms; another coefficient-space estimate
would be theatre.

Verdict: `[PROVED — PURE WOLD HALF-DENSITY PRODUCER REDUCTION; CANCELLATION OPEN]`.

---

## 61. Conjecture loop 37 — bounded Wold discrepancy and centered log connection

### Conjecture

Treat the depth-one Wold coefficient as a positive measure on the ordered prime-log mesh.  The
Euler depletion in (RJG170) has finite total mass, while Mertens' logarithmic prime measure has
bounded cumulative discrepancy from Lebesgue log mass.  Therefore the cumulative Wold mass should
satisfy

```text
W(N)=sum_(p<=N) c_1(p),
|W(N)-log N| <= C_M+C_trace.                            (RJG175)
```

At the `N`th prime cutoff, Abel summation should then retain phase and split every finite pure-Wold
prefix into a deterministic logarithmic-mesh current and one centered connection whose arithmetic
primitive is uniformly bounded.

### Closure

The conjecture is exact.  Lean proves the natural-number identity

```text
c_1(p) + (h(p)-c_1(p)) = log(p)/p,
```

including zero extension off the primes, summability and positivity of the Euler correction, and
(RJG175) for every natural cutoff.  It also proves that the first `N+1` ordered primes are exactly
the primes through `p_N`, so the same bound holds for

```text
D_N=sum_(n<=N)c_1(p_n)-log(p_N),
|D_N| <= C_M+C_trace.                                   (RJG176)
```

Writing `G_N(tau)=sqrt(p_N) F_tau(log p_N)`, exact finite Abel summation gives

```text
sum_(n<=N)c_1(p_n)G_n
  = G_N W_N + sum_(n<N) W_n(G_n-G_(n+1))

  = [G_N log(p_N)+sum_(n<N)log(p_n)(G_n-G_(n+1))]
    +[G_N D_N+sum_(n<N)D_n(G_n-G_(n+1))].               (RJG177)
```

No norm, rearrangement, asymptotic replacement, or RH premise enters (RJG177).  This is the first
exact Route-T representation in which the remaining arithmetic input is a uniformly bounded
primitive rather than a growing critical coefficient mass.

Lean status: `[FORMALIZED] [COMPILES]` in
`XiHeatCassiniWoldLogDiscrepancy.lean` and
`XiHeatCassiniWoldCenteredLogConnection.lean`.

### Hostile audit and higher principle

Bounded discrepancy is not yet a bound for the second bracket of (RJG177).  Taking absolute values
would charge total variation of the restored half-density profile; that profile carries precisely
the timelike radiation which made (RJG174) RH-complete.  Thus (RJG177) is genuine reduction, not
closure.

The higher invariant is now visible:

```text
critical coefficient growth
  = logarithmic reference transport + bounded arithmetic holonomy,

Route-T obstruction
  = phase-linear action of that holonomy on the non-normal mass half-wave. (RJG178)
```

Mertens controls the primitive, theta Green compensation controls the quotient current, and the
two-residue theorem controls its persistent asymptotic carrier.  What remains is their common
unsquared joint phase: a centered Wold holonomy/Green-current weld.  Any next conjecture that
separately bounds `D_N` and `G_n-G_(n+1)` repeats the total-variation failure and is rejected.

Verdict: `[PROVED — BOUNDED-DISCREPANCY LOG CONNECTION; JOINT PHASE WELD OPEN]`.

---

## 62. Conjecture loop 38 — Wold/theta-Green common-anomaly Ward identity

### Conjecture

The theta Green current and pure depth-one Wold current should not be treated as transverse
quantities.  The exact valuation-one decomposition (RJG170) suggests they are two representatives
of one quotient anomaly: replacing valuation one by pure Wold should remove only the positive
trace-class Euler depletion current.  Hence the joint packet

```text
Q_W(a,c,tau)=Theta_metric(a,c,tau)+i M_theta L_W(a,tau)
```

should satisfy an exact Ward identity whose surviving terms are archimedean, prime-square,
higher-prime-power, and trace-correction faces.

### Closure

The conjecture is exact.  For every legal pair of depths and every `Re(tau)>0`, Lean proves

```text
Q_W
 = Q_valuation-one - i M_theta R_trace
 = i M_theta [A_arch - (P_square + P_high) - R_trace].   (RJG179)
```

The trace correction has a prime-square majorant at quarter depth.  Pointwise vertical
Riemann--Lebesgue extinction plus dominated convergence therefore gives

```text
R_trace(sigma+i u) -> 0  as u -> +infinity.              (RJG180)
```

Consequently the Wold/theta packet is uniformly bounded on every positive vertical line and has
exactly the already-proved two-residue asymptotic carrier:

```text
sup_u |Q_W(sigma+i u)| < infinity,
Q_W(sigma+i u)-C_two-residue(sigma+i u) -> 0.            (RJG181)
```

No RH premise, added axiom, total-variation estimate, or coefficient-space closure enters these
statements.

Lean status: `[FORMALIZED] [COMPILES]` in
`XiHeatCassiniWoldThetaGreenCompensation.lean`.

### Hostile audit and higher principle

(RJG179)--(RJG181) do not separately bound theta current or pure Wold current.  They prove the
opposite structural fact needed to avoid a false coercivity programme: these currents are
anti-diagonal representatives of one anomaly modulo a finite dispersive ideal.  Any Gram or energy
argument declaring them orthogonal would contradict their exact Ward cancellation.

The higher principle is a quotient-current gauge law:

```text
theta Green representative - valuation-one representative
  = pure Wold representative modulo dispersive Euler trace.             (RJG182)
```

Persistent two-residue carrier belongs to this quotient class, not to either representative in
isolation.  Remaining obstruction is to resolve arithmetic holonomy inside this common phase
class.  Corpus Mertens exponential-rate theorem now predicts more than (RJG176): `D_N` converges,
so persistent holonomy should telescope to one static first-prime boundary atom and leave a
zero-tail primitive.

Verdict: `[PROVED — COMMON ANOMALY AND CARRIER RIGIDITY; HOLONOMY LIMIT OPEN]`.

---

## 63. Conjecture loop 39 — convergent Wold holonomy and static boundary charge

### Conjecture

The bounded primitive `D_N` in (RJG176)--(RJG178) should have a genuine limit.  Corpus already
contains an exponential-rate Mertens first theorem, while the Euler-depletion correction is a
positive summable measure.  Their difference therefore predicts a canonical Wold logarithmic
holonomy

```text
D_infinity = c_Mertens - mass(R_trace),
D_N -> D_infinity.                                      (RJG183)
```

Centering at this limit should expose a stronger Abel law: constant holonomy is an exact
coboundary and must telescope to a single boundary atom, leaving a residual primitive tending to
zero.

### Closure

The conjecture is exact.  Lean first identifies the repository's prime-window Mertens sum with the
sieve sum `mertensA`.  The existing exponential error theorem implies convergence of
`mertensA(N)-log N`; ordinary partial sums of the Euler trace correction converge to its `tsum`.
Combining these with (RJG170) proves (RJG183) both for natural cutoffs and ordered-prime cutoffs.

Define

```text
E_N = D_N-D_infinity.
```

Then Lean proves `E_N -> 0` and the exact finite telescope

```text
G_N D_N + sum_(n<N) D_n (G_n-G_(n+1))
 = D_infinity G_0
   + G_N E_N + sum_(n<N) E_n (G_n-G_(n+1)).             (RJG184)
```

Substitution into (RJG177) gives the sharpened pure-Wold law

```text
sum_(n<=N)c_1(p_n)G_n
 = logarithmic-mesh current
   + D_infinity G_0
   + zero-tail residual connection.                     (RJG185)
```

Thus the entire persistent bounded arithmetic obstruction is rank one in boundary location: it is
one fixed first-prime profile, not an infinite connection.  All remaining connection coefficients
vanish.

Lean status: `[FORMALIZED] [COMPILES]` in
`XiHeatCassiniWoldConvergentLogHolonomy.lean`.

### Hostile audit and pivot

`E_N -> 0` alone does not yield a uniform vertical-line bound after multiplying by adjacent profile
variation.  Arbitrarily slow convergence would still permit timelike radiation to outrun the
arithmetic tail.  Therefore (RJG184) removes the persistent infinite-dimensional obstruction but
does not close Route T.

The next conjecture must use the actual rate already latent in its proof.  Euler trace tail is
bounded by `O((log N)/N)`, faster than Mertens' `exp(-c sqrt(log N))`; hence

```text
|E_N| <= B exp(-c sqrt(log p_N))                         (RJG186)
```

eventually.  This is substantive because it converts residual holonomy from a qualitative null
sequence into a quantified arithmetic damping factor available for direct phase-gradient pairing.
If even (RJG186) loses to the timelike half-density variation, that failure will identify exact
radiation scale requiring theta-current cancellation rather than coefficient decay.

Verdict: `[PROVED — STATIC HOLONOMY CHARGE; QUANTITATIVE RESIDUAL RATE OPEN]`.

---

## 64. Conjecture loop 40 — exponential square-root-log holonomy damping

### Conjecture

The qualitative tail `E_N -> 0` in (RJG184)--(RJG186) should inherit the exponential
square-root-log remainder already proved for the repository's Mertens sum.  The only extra term is
the positive Euler-depletion trace, whose coefficient is pointwise `O(log n/n^2)` and therefore
has a strictly smaller tail.

### Closure

Lean proves the explicit trace estimate

```text
0 <= mass(R_trace)-sum_(n<=N)R_trace(n)
   <= 3(log N+1)/N.                                    (RJG187)
```

The existing Mertens exponential-rate center is identified with the selected limit constant by
uniqueness of limits.  Combining it with (RJG187) gives constants `B>=0`, `c>0` such that,
eventually,

```text
|E_N| <= B exp(-c sqrt(log p_N)).                        (RJG188)
```

Consequently every residual connection atom satisfies the phase-preserving estimate

```text
|E_N (G_N-G_(N+1))|
 <= B exp(-c sqrt(log p_N)) |G_N-G_(N+1)|.              (RJG189)
```

Lean status: `[FORMALIZED] [COMPILES]` in
`XiHeatCassiniWoldHolonomyExpRate.lean`.

### Hostile audit and pivot

(RJG188) is subpower damping.  It cannot beat the restored half-density factor `sqrt(p)` by
pointwise comparison: `sqrt(p) exp(-c sqrt(log p))` is unbounded.  Thus the conjecture succeeds as
arithmetic information but fails as a terminal norm estimate.  Any continuation that simply
inserts (RJG189) into total variation plays theorem theatre and recreates the timelike radiation
wall.

Verdict: `[PROVED — QUANTITATIVE HOLONOMY DAMPING; POINTWISE RADIATION CLOSURE IMPOSSIBLE]`.

---

## 65. Conjecture loop 41 — critical harmonic Fisher energy of residual holonomy

### Conjecture

Although (RJG188) loses pointwise against the half-density envelope, its square should be
integrable in the exact critical arithmetic coframe.  The natural measure is not counting measure
but the Route-T harmonic prime measure `dmu(p)=log(p)/p`.

### Closure

Burnol's unconditional prime Poisson summability absorbs every fixed logarithmic factor against
`exp(-2c sqrt(log p))/p`.  After clipping finitely many pre-asymptotic coordinates, Lean proves

```text
sum_N (log p_N/p_N) |E_N|^2 < infinity.                 (RJG190)
```

Thus centered Wold holonomy is a genuine finite-energy vector in the same critical coframe that
reconstructs the valuation-one Route-T source.  This is stronger than convergence or a pointwise
rate: it identifies a canonical Hilbert geometry for the residual arithmetic connection.

Lean status: `[FORMALIZED] [COMPILES]` in
`XiHeatCassiniWoldHolonomyFisherEnergy.lean`.

### Hostile audit and higher principle

Cauchy--Schwarz closes a phase-linear connection only if the transported profile has uniformly
bounded dual Dirichlet energy.  The restored timelike half-density has precisely the opposite
radiation growth, so (RJG190) alone cannot supply that dual bound.  Finite Fisher energy is a
positive survivor, not an RH proof.

The accumulated structure now has a one-dimensional Hodge form: static holonomy is one harmonic
boundary charge, `E` is a finite-energy exact component, and scalar theta--Wold compensation sees
only their common anti-diagonal anomaly.  Missing datum must separate source phase grades before
the pinned scalar trace.  Norm completion cannot do so.

Verdict: `[PROVED — FINITE CRITICAL HOLONOMY ENERGY; SOURCE-LEVEL PHASE GRADE OPEN]`.

---

## 66. Conjecture loop 42 — exterior-reflection Boolean grade duality

### Conjecture

The opposite safe exterior theta line might supply a second scalar Ward equation.  If reflection
preserved the Wold sign while reversing the theta current, adding the two bounded packets would
isolate the RH-strength Wold producer.

### Exact reflection law

The conjectured second equation is false, but its failure exposes an exact Boolean grading.  Under
simultaneous exterior-height and frequency reflection,

```text
zeta_(-c)(-x)=-zeta_c(x),
MassTest_(-c)(x)=MassTest_c(-x),
ThetaRow_(-c)(-x)=-ThetaRow_c(x).                       (RJG191)
```

The first identity is algebraic, the second uses evenness of the analytic Xi-mass test, and the
third uses oddness of `XiC'/XiC`.  Hence both the phase-linear theta packet and its polarized Green
realization belong to the odd exterior grade:

```text
Theta(-c)=-Theta(c),
Green(-c)=-Green(c).                                    (RJG192)
```

Pure Wold current has no exterior-line parameter and belongs to the even grade.  Therefore the
two plus-sign packets satisfy the exact parity projection

```text
(Green(c)+i d Wold)+(Green(-c)+i d Wold)=2 i d Wold.    (RJG193)
```

The actual reflected Ward law must reflect the complete odd-grade packet, including the Wold
sign:

```text
Green(-c)-i d Wold=-(Green(c)+i d Wold).                (RJG194)
```

It is unconditionally bounded, but is only the negative of the known equation.  Define the
wrong-grade reflected packet by retaining the plus Wold sign on the left line.  Since the right
packet is already bounded and `d != 0`, Lean proves

```text
WrongGradeReflectedBound
 iff PureWoldBound
 iff RH.                                                (RJG195)
```

Lean status: `[FORMALIZED] [COMPILES]` in
`XiHeatCassiniThetaExteriorReflectionGradeLock.lean`.

### Hostile audit and higher universal principle

Exterior reflection does not create missing quadrature.  It defines a `Z/2` representation:
theta/Green is odd, Wold arithmetic is even, and known Ward identity controls only one
anti-diagonal grade.  Desired RH estimate is exactly a grade-changing law, not stronger decay or
another scalar norm.

This reinterprets previous stalls uniformly.  Fisher squaring forgets the Boolean grade; scalar
theta--Wold compensation identifies only anti-diagonal quotient; reflected scalarization repeats
same character.  Existing Hedenmalm--Euler reflection-admission fracture additionally rules out a
fixed-domain finite-energy linear transport at nonzero displacement.  A viable producer must
therefore be source-selected and domain-changing (or equivalently carry an unbounded closed
supercharge) while preserving the phase-linear current.  Searching for a bounded same-domain
intertwiner is now a proved dead route.

Verdict: `[PROVED — EXACT EXTERIOR BOOLEAN GRADE; WRONG-GRADE LAW IS RH-EQUIVALENT]`.

---

## 67. Conjecture loop 43 — residual holonomy landing in source-selected Fisher graph domain

### Conjecture

The Boolean-grade theorem says a successful flip must be graph-singular and source-selected.
Section 65 supplied finite energy only in Route T's harmonic coframe `log(p)/p`.  Corpus has two
independently constructed source-selected prime measures: diagonal Euler activation Fisher density
and literal strict-preclosure essential edge.  Both are uniformly comparable to `1/p`.  Therefore
the centered Wold residual should land in their Hilbert and prime-log graph domains without any
new decay hypothesis.

### Closure

Transport the ordered residual through the prime enumeration and write it as `E(p)`.  Lean proves

```text
sum_p (1/p) |E(p)|^2 < infinity.                         (RJG196)
```

The activation Fisher density `d_F(p)=p/(p+1)^2` and actual essential-edge coordinate
`d_A(p)=1/p-p/farPrime(p)^2` satisfy `0<=d_F,d_A<=1/p`.  Consequently

```text
sum_p d_F(p)|E(p)|^2 < infinity,
sum_p d_A(p)|E(p)|^2 < infinity.                         (RJG197)
```

More strongly, the original `log(p)/p` energy is exactly enough for the graph norm of the
unbounded prime-log half-gradient:

```text
sum_p log(p)d_F(p)|E(p)|^2 < infinity,
sum_p log(p)d_A(p)|E(p)|^2 < infinity.                   (RJG198)
```

The two residual energy densities differ by a summable sequence.  Thus the Route-T residual lands
in one concrete source-selected graph domain represented equally by activation Fisher and actual
essential edge modulo trace class.

Lean status: `[FORMALIZED] [COMPILES]` in
`XiHeatCassiniWoldHolonomyActivationFisherLanding.lean`.

### Hostile audit and pivot

(RJG198) is genuine graph-domain landing, but it supplies no operator that changes the exterior
Boolean character.  It proves arithmetic residual regularity is sufficient for the first
unbounded log derivative.  Remaining obstruction is constructing the source-derived closed
off-diagonal action and proving it sends odd theta grade to even Wold grade without erasing the
unsquared current.

Verdict: `[PROVED — SOURCE-SELECTED FISHER GRAPH LANDING; GRADE ACTION OPEN]`.

---

## 68. Conjecture loop 44 — all-orders prime-log graph smoothness

### Conjecture

First graph-domain landing might be accidental: one factor of `log(p)` is already present in the
critical harmonic coframe.  To support a genuine closed grade operator, residual should survive
every finite power of signed prime-log generator.

### Closure

Square-root-log exponential rate absorbs every polynomial in `log(p)`.  For every `k : Nat`, Lean
proves unconditionally

```text
sum_p log(p)^(2k) d_F(p) |E(p)|^2 < infinity,
sum_p log(p)^(2k) d_A(p) |E(p)|^2 < infinity.            (RJG199)
```

Proof first establishes harmonic majorant

```text
sum_p log(p)^(2k) exp(-2c sqrt(log(p))) / p < infinity
```

from Burnol Poisson-subordinate summability, clips finite exceptional prefix in eventual holonomy
rate, then transports through prime enumeration.  Source-density bounds finish activation-Fisher
and literal essential-edge forms.

Lean status: `[FORMALIZED] [COMPILES]` in
`XiHeatCassiniWoldHolonomyLogSmooth.lean`.

### Hostile audit and pivot

Arithmetic residual is a smooth vector for signed prime-log generator: no finite differential
order causes admission loss.  This is stronger than first graph landing and removes polynomial
regularity as possible obstruction.

It does not imply analytic-vector or multiplicative-height Köthe landing.  Powers of
multiplicative height are exponential weights in `log(p)`; square-root-log decay does not certify
them.  Correct next domain is doubled positive/negative prime-log boundary, where Deninger
`i sign(log p)` Hodge action can change Boolean sheet grade without demanding false power decay.

Verdict: `[PROVED — ALL FINITE LOG-GRAPH ORDERS; DOUBLED HODGE GRADE ACTION NEXT]`.

---

## 69. Conjecture loop 45 — concrete Deninger boundary grade and observer parity

### Conjecture

All-orders prime-log smoothness should permit a genuine source-selected grade change on the
doubled prime boundary.  The remaining question is whether scalar observation preserves the
unsquared residual or repeats the Fisher-squaring loss.

### Closure

Double each ordinary prime into sheets with frequencies `+log(p)` and `-log(p)`, and put the same
activation-Fisher amplitude on both sheets:

```text
x(p,+)=x(p,-)=sqrt(d_F(p)) E(p).
```

Lean constructs this as an honest `DiagonalL2` vector in every polynomial domain of the maximal
signed-log generator.  Deninger's canonical boundary Hodge operator acts pointwise by

```text
H x(p,+)= i x(p,+),
H x(p,-)=-i x(p,-),
H^2 x=-x,             ||H x||=||x||.                    (RJG200)
```

Thus `H` sends the even residual to the odd Boolean sheet grade without any multiplicative-height
admission claim.  Observer parity is decisive.  The even sheet sum annihilates the transformed
residual at every prime, whereas odd sheet contrast retains its sign:

```text
Hx(p,+)+Hx(p,-)=0,
Hx(p,+)-Hx(p,-)=2 i sqrt(d_F(p)) E(p).                  (RJG201)
```

The same dichotomy survives quadratic contraction.  Same-grade pairing cancels, while cross-grade
pairing recovers exact activation-Fisher energy:

```text
conj(x_+) Hx_+ + conj(x_-) Hx_- = 0,
conj(x_+) Hx_+ - conj(x_-) Hx_- = 2 i d_F(p) E(p)^2.   (RJG202)
```

The real coefficients of the surviving cross-grade Fisher flux are summable over all primes.

Lean status: `[FORMALIZED] [COMPILES]` in
`XiHeatCassiniWoldDeningerBoundaryGrade.lean`.

### Hostile audit and pivot

Concrete source-grade action now exists; missing theorem is no longer construction of a Boolean
flip.  Failure is observation: every reflection-even scalar observer is provably blind, while a
reflection-odd observer preserves the unsquared arithmetic residual.  Fisher squaring was not
merely too weak—it selected the wrong observer character.

To reach physical Route-T terminal flux, the odd observer must undo the activation-Fisher square
root and restore mass half-density.  Exact multiplier of that deconvolution is next object; its
growth determines whether source transgression can land on physical boundary.

Verdict: `[PROVED — CONCRETE UNITARY GRADE CHANGE; REFLECTION-ODD PHYSICAL OBSERVER OPEN]`.

---

## 70. Conjecture loop 46 — exact physical observer and multiplicative-height wall

### Conjecture

The odd Hodge observer from Section 69 preserves `sqrt(d_F(p)) E(p)`, while Route T's physical
terminal flux contains `sqrt(p) E(p)`.  Exact deconvolution coefficient should identify whether
missing landing is another finite log derivative or a genuinely different horizontal grade.

### Closure

For activation Fisher density `d_F(p)=p/(p+1)^2`, Lean proves

```text
sqrt(d_F(p)) = sqrt(p)/(p+1),
sqrt(p)/sqrt(d_F(p)) = p+1.                              (RJG203)
```

Thus physical observation costs exactly one multiplicative-height step.  It is not an arbitrary
growth factor: corpus comparison transport identifies it literally as

```text
p+1 = fisherDeconvolvedComparisonWeight(-1,p).           (RJG204)
```

The sharp same-carrier orientation theorem then proves this multiplier is unbounded and does not
preserve the fixed Fisher-deconvolved `ell^1` ideal.  Physical observation lies in the forbidden
negative horizontal chamber.

Source probability gives a second exact interpretation.  At the critical reciprocal-prime node,
the occupancy probability is `pi_p=1/(p+1)`, so physical coefficient is `pi_p^{-1}`.  Moreover

```text
d_F(p)(p+1) = - OccupancyScore(p,true),
sqrt(p) = - OccupancyScore(p,true)/sqrt(d_F(p)).          (RJG205)
```

Restored physical half-density is therefore the occupied Boolean score whitened by its literal
source Fisher metric.  This explains both its canonical provenance and its rare-event
unboundedness.

For every mass profile and ordered prime, Lean proves exact physical landing

```text
sqrt(d_F(p_N)) E_N * ((p_N+1) F_u(log p_N))
  = sqrt(p_N) F_u(log p_N) E_N,

OddHodgePhysicalObserver(p_N)
  = 2 i * ResidualTerminalFlux_N.                        (RJG206)
```

Finally, strict domain separation is constructive.  The single probe `x(p)=1/p` satisfies

```text
for every k, sum_p |log(p)^k x(p)|^2 < infinity,
but sum_p |(p+1)x(p)|^2 = infinity.                      (RJG207)
```

Hence intersection of all finite signed-log graph domains is provably insufficient for physical
observation; no finite-order log regularity argument can close this step.

Lean status: `[FORMALIZED] [COMPILES]` in
`XiHeatCassiniWoldDeningerPhysicalObserverWall.lean`.

### Hostile audit and pivot

This closes observer identification but not its uniform vertical bound.  Same-carrier bounded
operator strategy is now rigorously dead: required observer is exactly negative-grade transport,
and an explicit smooth vector witnesses failure.

Positive survivor is sharper than a no-go.  Physical multiplier is canonical inverse occupancy,
and resulting `sqrt(p)` is Fisher-whitened Boolean score.  Since `sqrt(p)=exp(log(p)/2)`, same factor
should also be internal to mass geometry as lower contour translation by `-i/2`.  Every legal
Route-T aperture has width greater than `1/2`; next test is whether joint source pairing moves the
observer onto that legal strip boundary before norms.

Verdict: `[PROVED — EXACT NEGATIVE-GRADE PHYSICAL OBSERVER; FINITE LOG SMOOTHNESS STRICTLY FAILS]`.

---

## 71. Conjecture loop 47 — internalizing physical observation as half-strip transgression

### Conjecture

Section 70 identified physical restoration as `sqrt(p)=exp(log(p)/2)`.  Fourier covariance suggests
this is exactly a downward imaginary translation of mass integration contour by `1/2`.  Since every
legal Route-T aperture satisfies `a>1/2`, physical observer may be internal to analytic source
geometry even though it is unbounded on abstract Fisher boundary.

### Closure

For every legal lower depth `0<=c<a`, Lean proves exact contour covariance

```text
integral_R g_tau(x-c i) exp(-i log(p) x) dx
  = exp(c log(p)) F_tau(log(p)).                         (RJG208)
```

Proof applies full-line horizontal contour transport to the complete analytic Fourier kernel
before splitting phase.  At critical half depth,

```text
integral_R g_tau(x-i/2) exp(-i log(p) x) dx
  = sqrt(p) F_tau(log(p)).                               (RJG209)
```

No limiting argument or off-strip continuation enters: `1/2<a` is exactly Route T's legal aperture
condition.  Therefore ordered physical residual terminal flux has joint-pairing form

```text
ResidualTerminalFlux_N
  = LowerHalfShiftProfile_tau(p_N) E(p_N).               (RJG210)
```

Combining with Section 70 gives direct source-grade landing

```text
OddHodgePhysicalObserver(p_N)
  = 2 i LowerHalfShiftProfile_tau(p_N) E(p_N).           (RJG211)
```

Lean status: `[FORMALIZED] [COMPILES]` in
`XiHeatCassiniWoldHalfShiftPhysicalObserver.lean`.

### Hostile audit and higher principle

Unbounded diagonal multiplier and legal contour translation are two charts of same object.
Abstract all-log-smooth boundary cannot admit `exp(|D|/2)`, but actual Xi-mass test already carries
strip analyticity wide enough to realize that analytic-vector step exactly.  Thus multiplicative
wall is not mathematical impossibility; it says operator must act jointly on arithmetic residual
and analytic mass source, never on residual Hilbert vector alone.

This reframes every previous stall.  Termwise norms separate Fisher coefficient from mass strip and
see forbidden inverse occupancy.  Exact joint pairing absorbs inverse occupancy into source contour
geometry.  Remaining hard theorem is now sharply localized: control finite lower-half-strip
connection pairing while retaining adjacent-prime phase cancellation.  No further residual-only
regularity can help.

Verdict: `[PROVED — PHYSICAL OBSERVER IS LEGAL HALF-STRIP TRANSGRESSION; JOINT CONNECTION BOUND OPEN]`.

---

## 72. Conjecture loop 48 — lower-half connection and reciprocal prime-log telescope

### Conjecture

After Section 71 internalizes `sqrt(p)` into the lower contour, retain the whole centered Wold
primitive under that integral and perform finite Abel transport there.  Adjacent phases should
contribute a prime-log gap, and exponential square-root-log residual decay may then become
summable without requiring a prime-gap asymptotic.

### Closure

For `h_N=log(p_N)`, `E_N` the centered Wold residual, and
`q_N(x)=exp(-i h_N x)`, Lean constructs one joint lower-boundary kernel and proves

```text
JointKernel_N(x)
  = g_tau(x-i/2) [E_N q_N(x) + sum_(n<N) E_n(q_n(x)-q_(n+1)(x))],

integral_R JointKernel_N
  = ResidualTerminalFlux_N + sum_(n<N) ResidualConnectionAtom_n.    (RJG212)
```

No norm or sheet projection occurs before adjacent-prime cancellation.  The phase kernel also has
the exact local arithmetic normal form

```text
E_0 q_0 + sum_(n<N) [woldCoeff(p_(n+1))-(h_(n+1)-h_n)] q_(n+1).
```

Bertrand's theorem supplies the elementary height comparison `h_(n+1)<=2h_n`.  Positivity then
gives the reciprocal charge inequality

```text
(h_(n+1)-h_n)/h_n^2
  <= 2(1/h_n-1/h_(n+1)),

sum_n (h_(n+1)-h_n)/h_n^2 < infinity.                    (RJG213)
```

Since every `exp(-c sqrt(h))` is bounded by `C/h^2`, the proven Wold rate implies the new
finite-variation law on the *actual prime-log mesh*

```text
sum_n |E_n| (h_(n+1)-h_n) < infinity.                    (RJG214)
```

The Fourier chord estimate

```text
|q_n(x)-q_(n+1)(x)| <= (h_(n+1)-h_n)|x|
```

therefore proves absolute convergence of the physical residual phase connection at every source
coordinate and convergence of finite primitive kernels to

```text
sum_n E_n(q_n-q_(n+1)).                                  (RJG215)
```

The formal proof caught and removed an extra `E_0 q_0` in the initially conjectured primitive
limit: that base term belongs to the increment normal form, not to the sum of primitive connection
atoms.

Lean status: `[FORMALIZED] [COMPILES]` in
`XiHeatCassiniWoldLowerHalfShiftConnectionKernel.lean` and
`XiHeatCassiniWoldLowerHalfShiftGapSummability.lean`.

### Hostile audit and higher principle

This is genuine new quantitative knowledge: earlier pointwise residual decay did not give total
variation, while the physical half-shift exposes exactly the mesh factor that makes a reciprocal
telescope possible.  It closes prime-height amplification inside the residual phase connection
without PNT-scale gap estimates.

It does **not** yet prove the uniform vertical line bound.  Pointwise absolute convergence of the
phase connection may be integrated for each fixed `tau`, but taking the lower-contour mass-test
norm first costs exponential vertical growth.  The explicit logarithmic-mesh main current also
remains outside this residual theorem.  The obstruction has moved cleanly: arithmetic residual
summation is closed; joint timelike/glancing transport in vertical time, together with the main
log-mesh current, is open.

Higher principle: prime height is not the correct local norm variable after physical observation.
The invariant quantity is residual variation against the Stieltjes mesh `dh`; Bertrand bounds its
reciprocal curvature, and Wold decay supplies all missing damping.  Next conjecture must preserve
this Stieltjes connection while treating vertical oscillation, rather than reverting to termwise
prime amplitudes.

Verdict: `[PROVED — PHYSICAL RESIDUAL HAS FINITE PRIME-LOG VARIATION; VERTICAL GLANCING AND MAIN MESH OPEN]`.

---

## 73. Conjecture loop 49 — prime-log quadrature and the exact mean-square-gap threshold

### Conjecture

The logarithmic main connection left by the centered Wold recut should be compared with the
already-bounded continuous growing-profile integral before estimating individual prime samples.
Right-endpoint quadrature ought to expose the precise arithmetic cost, rather than the much larger
termwise half-density envelope.

### Closure

For `h_N=log(p_N)`, `delta_N=h_(N+1)-h_N`, and

```text
G_u(h)=exp(h/2) Fourier[g_(sigma+iu)](h),
```

Lean proves the exact finite identity

```text
LogMeshFlux_N
 = h_0 G_u(h_0) + sum_(n<N) delta_n G_u(h_(n+1)).       (RJG216)
```

Thus the main Wold logarithmic connection is literal right-endpoint quadrature of the same
continuous current whose cone integral is already uniformly bounded in
`XiMassCriticalIntegerFace.lean`.  Naming the derivative gives

```text
G'_u(h)=exp(h/2)[(1/2) Fourier[g_(sigma+iu)](h)
                         + Fourier[-ix g_(sigma+iu)](h)],
|G'_u(h)| <= exp(h/2) J_sigma,                            (RJG217)
```

with `J_sigma` independent of `u`.  Integration by parts on one cell gives the exact Peano-kernel
formula

```text
delta G_u(s)-integral_r^s G_u(h) dh
 = integral_r^s (h-r)G'_u(h) dh,
|cell error| <= delta^2 exp(s/2) J_sigma.                 (RJG218)
```

For consecutive primes `p<q`, elementary logarithmic concavity and Bertrand give

```text
delta <= (q-p)/p,
delta^2 exp(log(q)/2)
 <= 2 ((q-p)/p)^2 sqrt(p).                                (RJG219)
```

Consequently the entire main-mesh quadrature error is reduced, without a hidden vertical
parameter, to the positive arithmetic series

```text
sum_n (p_(n+1)-p_n)^2 / p_n^(3/2).                        (RJG220)
```

Maynard's unconditional mean-square consecutive-prime-gap estimate
`sum_(p_n<=X) (p_(n+1)-p_n)^2 <<_epsilon X^(5/4+epsilon)` makes (RJG220) convergent by dyadic
summation.  This literature input has been audited against the primary paper, but is not yet
formalized in the corpus; it is not used as a Lean premise.

Lean status: `[FORMALIZED] [COMPILES]` for (RJG216)--(RJG219) in
`XiHeatCassiniLogMeshPrimeGapQuadrature.lean`.  (RJG220) remains an unconditional theorem target,
not an assumption.

### Hostile audit and higher principle

This is genuine obstacle reduction.  Previous estimates charged `sqrt(p)` to every prime.  The
joint Stieltjes comparison charges only square mesh curvature, and it identifies a known
unconditional mean-square theorem strong enough to close the whole logarithmic main layer.  It
does not close the residual Wold connection: that layer contains the half-strip timelike radiation
and cannot be absorbed into the positive quadrature error.

Higher principle: main mesh and Wold residual are different microlocal defects.  Main mesh is
second-order partition curvature and belongs to mean-square prime-gap theory.  Residual is a
signed boundary source and belongs to timelike propagation.  Treating either with the other's norm
loses the exact cancellation and recreates the critical square-root wall.

Verdict: `[PROVED — MAIN LOG MESH REDUCED TO ONE UNCONDITIONAL MEAN-SQUARE PRIME-GAP THEOREM; RESIDUAL TIMELIKE SOURCE STILL OPEN]`.

---

## 74. Conjecture loop 50 — complete smooth jet of the residual boundary source

### Conjecture

The square-root-log decay of the centered Wold primitive, combined with one adjacent prime-log
chord, should survive every polynomial frequency moment.  If so, the infinite physical residual
phase connection is not merely pointwise convergent: it has a locally uniform derivative tower.

### Closure

For every natural `k`, Lean proves

```text
sum_N h_(N+1)^k |E_N| delta_N < infinity.                 (RJG221)
```

The proof uses only the already-formalized Wold rate, Bertrand's
`h_(N+1)<=2h_N`, polynomial absorption into `exp(-c sqrt(h_N))`, and the reciprocal-log telescope
from (RJG213).  Define the `k`th edge jet

```text
J_(k,N)(x)
 = E_N[(-i h_N)^k exp(-i h_N x)
       -(-i h_(N+1))^k exp(-i h_(N+1)x)].
```

Lean proves the exact derivative ladder

```text
d/dx J_(k,N)(x)=J_(k+1,N)(x),                             (RJG222)
```

and the gap-preserving bound

```text
|J_(k,N)(x)|
 <= |E_N| delta_N
      [h_(N+1)^k |x| + k h_(N+1)^(k-1)].                 (RJG223)
```

Hence every jet series is absolutely summable at every real `x`.  On each unit neighborhood the
`(k+1)`st series has one summable majorant, so the smooth-series theorem applies recursively:

```text
K_k(x)=sum_N J_(k,N)(x),
K'_k=K_(k+1),
K_0 in C^infinity(R).                                    (RJG224)
```

Lean status: `[FORMALIZED] [COMPILES]` in
`XiHeatCassiniWoldLowerHalfShiftGevreyKernel.lean`.

### Hostile audit and higher principle

(RJG221)--(RJG224) are new physical regularity, not Hilbert-graph relabeling: derivatives are
actual real-boundary derivatives of the infinite residual source, and all interchanges are backed
by locally uniform summable majorants.

They do not authorize the fixed lower-half contour at the infinite-source level.  `C^infinity`
regularity and all polynomial moments are weaker than exponential frequency moments.  The
half-density observer applies `exp(h/2)`, so calling this kernel analytic or claiming its smoothness
closes vertical propagation would be false.  Quantitative Gevrey constants are also not claimed by
the Lean theorem.

Higher principle: finite physical half-shift and infinite residual limit do not commute for purely
regularity-theoretic reasons.  The residual is a smooth boundary distribution whose forbidden
analytic continuation is exactly where timelike Route-T information lives.  A successful next
step must identify that analytic wavefront with the Xi divisor carrier, or preserve finite-stage
source/divisor cancellation through the limit; another residual norm cannot cross the wall.

Verdict: `[PROVED — RESIDUAL CONNECTION IS C-INFINITY WITH EXPLICIT SUMMABLE JETS; ANALYTIC HALF-SHIFT/WAVEFRONT REMAINS THE RH-STRENGTH WALL]`.

---

## 75. Conjecture loop 51 — one-sided Hardy polarization of the residual source

### Conjecture

Section 74 treated the residual kernel only on the real source boundary.  Its phases all have the
same negative-frequency orientation.  Complexifying the source coordinate should therefore expose
one legal analytic side even though the physical upper half-shift remains unavailable.

### Closure

For `h_N=log(p_N)`, `delta_N=h_(N+1)-h_N`, and `Im z<=0`, Lean proves

```text
|exp(-i h_N z)| <= 1,
|exp(-i h_N z)-exp(-i h_(N+1) z)| <= 2 delta_N |z|.      (RJG225)
```

The second estimate retains the full prime-log gap.  Combining it with (RJG214) makes every
complex edge series absolutely summable on the closed lower half-plane.  Its derivative atoms
retain the same gap with one logarithmic moment:

```text
|d/dz [E_N(exp(-i h_N z)-exp(-i h_(N+1) z))]|
 <= |E_N| delta_N [2 h_(N+1)|z|+1].                      (RJG226)
```

The all-moment theorem from Section 74 supplies locally uniform derivative majorants on every
lower-half-plane ball.  Termwise holomorphic differentiation therefore gives an unconditional
extension

```text
K(z)=sum_N E_N(exp(-i h_N z)-exp(-i h_(N+1) z)),
K holomorphic on {Im z<0},
K(x)=K_0(x) for x real.                                  (RJG227)
```

Let

```text
V=sum_N |E_N| delta_N < infinity.
```

The same chord bound survives the infinite sum and proves the global Hardy estimate

```text
|K(z)| <= 2 V |z|               (Im z<=0),
|K(z)/z| <= 2 V                 (Im z<0).                 (RJG228)
```

Thus the coordinate-divided residual is a bounded holomorphic carrier on the whole lower
half-plane, not merely a smooth real-boundary function.

Lean status: `[FORMALIZED] [COMPILES]` in
`XiHeatCassiniWoldResidualHardyPolarization.lean`.

### Hostile audit and higher principle

This corrects the coarse formulation at the end of Section 74.  The residual analytic wavefront is
not unknown on both sides.  It is completely polarized: the lower side is an unconditional bounded
Hardy carrier after division by `z`; only the upper side required by the physical half-density
observer remains inaccessible to the defining series.

(RJG228) alone does not prove the Route-T vertical line bound.  Using a lower-half-plane sup norm
against an absolute mass-test norm would still pay exponential vertical growth.  The new theorem is
useful because it changes the next question from regularity to continuation of one explicit
one-sided carrier.  On the Laplace ray `z=-i s`, `Re s>0`, finite Abel transport expresses this
carrier through the local increments

```text
E_(N+1)-E_N = woldCoeff(p_(N+1))-delta_N.
```

The Wold part is algebraically a four-shift finite difference of the derivative of complex prime
zeta; the mesh part is its ordered prime-log quadrature.  Next conjecture must identify that exact
safe-half-plane Laplace symbol and audit whether its upper continuation is precisely the existing
Xi divisor carrier.  This is a divisor-bearing pivot, not another residual norm.

Verdict: `[PROVED — RESIDUAL WAVEFRONT IS ONE-SIDED; DIVIDED SOURCE IS A GLOBAL LOWER-HARDY CARRIER; UPPER LAPLACE/DIVISOR CONTINUATION OPEN]`.
