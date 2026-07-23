# CCM first-clock direct positive factorization attack

- **ID:** `ccm-first-clock-direct-positive-factorization-attack`
- **Stage:** `1-in-progress`
- **Type:** DIRECT RH ATTACK
- **Status:** `[ACTIVE] [NO HYPOTHESES ALLOWED]`
- **Endpoint:** `CCMFirstClockPublishedSourceNonnegative ↔ RiemannHypothesis`

## Target

For every `L ≥ π/2`, prove directly from the literal published CCM source

```text
B₁(L)=ccmPublishedSourceSineCoefficient(L/2,2π/L) ≥ 0.
```

By the existing Lean theorem
`ccmFirstClockPublishedSourceNonnegative_iff_rh`, this is an unconditional proof of RH.

## Closed corpus inputs

1. The continuous Gamma--polar half-wave budget is strictly positive.
2. Every finite von Mangoldt--Gamma anomaly aperture has strict common all-depth orientation.
3. The first-clock sign is exactly

```text
π B₁(L)=C(L)+P₊(L)-P₋(L).
```

The present attack does not revisit these facts. It must construct the missing exact positive
factorization of the complete expression, including prime and Gamma--polar terms before any norm
or positivity argument.

## Active conjecture: completed multiplicative Green square

Let `x=exp(L/2)`. Rewrite the finite prime term using the exact identity
`Λ * 1 = log`, on the multiplicative triangle `dm≤x²`. Pair this discrete triangle with the
Stirling/Gamma continuous triangle before applying the first sine clock.

**Conjecture CPGS.** There is a source-defined kernel `K_L(d,m)` and an explicit boundary vector
`g_L`, both fixed by the Dirichlet hyperbola decomposition and Binet/Stirling completion, such
that

```text
π B₁(L)
 = Σ_(dm≤x²) |K_L(d,m)-K_L(m,d)|²
   + ||g_L||².
```

No term on the right may be defined from `B₁`, Xi zeros, a target Gram factorization, or an
RH-equivalent sign. The first task is symbolic derivation of the only possible kernel from
`Λ*1=log`; coefficient mismatch or an unavoidable signed boundary falsifies CPGS.

## Falsifiers

1. Möbius coefficients survive outside a square and have no Gamma partner.
2. The triangular boundary produces the known counter half-wave with the same sign.
3. Symmetrization erases irreducible prime contributions.
4. The derived square is only a restatement of `B₁≥0`.

## Log

- 2026-07-23 — Started direct attack after corpus audit confirmed orientation and the
  source-to-RH transfer are already closed.
- 2026-07-23 — **CPGS falsified.** Exact harmonic-floor mapping-cone identities already in the
  corpus reduce the proposed Dirichlet-hyperbola/Stirling completion to the null-gauged Möbius
  moving front. Its Mellin transform retains every off-critical zeta pole; a positive-square
  factorization of that scalar is therefore the RH statement, not its proof. The surviving
  direct source object is the finer future-dressed causal LCM ridge discarded by scalar collapse.
- 2026-07-23 — **Gamma-completed Boolean/ANOVA square falsified before formalization.**  The exact
  CRT transform has two nonzero resonance ridges, and the future-alias probability operator has
  sharp norm one.  Centering both ridges gives
  `(P_z(x)-V_z)(P_z(y)-V_z)` by `(PF19)`, while the universal stopped-compensator identity
  `(ST3)--(ST4)` reinserts the deleted marginal currents as the same physical endpoint defect.
  Thus neither the continuous Gamma budget nor future Möbius dressing turns the response into a
  top Boolean interaction with a product contraction.  Any surviving factorization must join the
  common physical profile globally across `h,p,a,r` without deleting or separately estimating
  either ridge.
- 2026-07-23 — **Half-gap phase-product mechanism classified and rejected at physical connector.**
  Half-gap twisting makes each normalized quadratic-root response real.  For a genuinely
  multiplicative response packet, complete future dressing has the exact product

  ```text
  product_(q in S) [1-theta_q(1+u_q)].
  ```

  It is nonnegative for every `u_q in [-1,1]` exactly up to the sharp local density threshold
  `theta_q<=1/2`; a singleton with `u_q=1` gives `1-2 theta_q`.  This is formalized in
  `CCMHalfGapFutureDressingCone.lean`.

  The physical anchored response `(AC13)` is not such a packet: inserting a future divisor `r`
  changes every source sample from `hat(W)_h(u/c)` to `hat(W)_h(u/(cr))`, and the primitivity
  restriction changes with `r`.  Thus the common clipped profile cannot be pulled out as local
  `u_q` factors.  The exact product theorem applies to a fixed reduced-frequency fibre already
  collapsed by `(AC10)`, not to the global `h,p,a,r` joining in `(AC25)`.  Claiming otherwise
  deletes the physical scale coupling and proves a different positive model.

## Active successor: ax+b edge-subdivision transfer

The hard critical weight has a source-native non-diagonal realization which does not freeze the
physical profile.  On complex edge sequences put

```text
(A_q u)(n)=q^(-1/2) sum_(0<=a<q) u(qn+a),              (AS1)
d_F(n)=F(n+1)-F(n).
```

For every multiplicative `F` with `F(0)=0`, exact path subdivision gives

```text
sum_(0<=a<q)d_F(qn+a)
 =F(q(n+1))-F(qn)
 =F(q)d_F(n),                                           (AS2)

A_q d_F=q^(-1/2)F(q)d_F.                               (AS3)
```

The operators are contractions on `ell^2(N)` by blockwise Cauchy--Schwarz, their adjoints repeat
one coarse coordinate uniformly over its `q` fine edges, and

```text
A_m A_q=A_(mq),   A_q A_q^*=I.                         (AS4)
```

For

```text
F_t(0)=0,   F_t(n)=exp(i t log n), n>=1,
d_t=d_(F_t),
```

Lean proves the character law `F_t(ab)=F_t(a)F_t(b)` and hence `(AS2)--(AS3)` become

```text
A_q d_t=q^(-1/2+it)d_t.                                (AS5)
```

Therefore the literal hard-cutoff prime clock is the joint-eigenvalue of one finite, source-defined
transfer operator, already at its distinguished initial edge:

```text
T_L=sum_(2<=q<=exp L) Lambda(q) A_q,

Im (T_L d_t)(0)
 =sum_(2<=q<=exp L) Lambda(q)/sqrt(q) sin(t log q)
 =P(L,t).                                               (AS6)
```

This is a complete paper proof of `(AS1)--(AS6)` and uses no estimate on primes.  Its new content
relative to the corpus is the common ax+b edge carrier: multiplication by `q` acts by exact
subdivision of the additive Gamma/successor path.  Consequently future insertion changes the
profile at the correct physical scale automatically; the false fixed-fibre pullout rejected above
is not used.

The representation is not yet positivity.  A generic numerical-range estimate for `T_L` is
impossible: its skew part has no fixed sign, and replacing the distinguished joint coboundary by
an arbitrary vector loses the source.  The RH-bearing conjecture is now narrower and falsifiable:

**Conjecture AES (arithmetic edge sewing).**  The Gamma--polar reflection operator obtained from
the additive successor boundary determinant is the Schur complement of the noncommuting aligned
block partitions `A_q^*A_q`, and on the distinguished first-clock coboundary it satisfies

```text
Im <d_(2pi/L),(T_L+i G_L)d_(2pi/L)> >=0,                (AS7)
```

with

```text
<d_(2pi/L),G_L d_(2pi/L)>/||d_(2pi/L)||^2
 =C_Gamma(L).                                           (AS8)
```

`G_L` must be derived from the successor/Gamma determinant before evaluating `d_t`; taking
`G_L=C_Gamma(L)I` is rejected as circular.  A proof of `(AS7)--(AS8)` composes immediately with
`pi_mul_ccmPublishedSourceSineCoefficient_eq_halfWaveBudget_add_prime` and
`ccmFirstClockPublishedSourceNonnegative_iff_rh`.

Hostile tests:

1. establish `(AS8)` from the Gamma shift recurrence, not from the target scalar;
2. retain noncommuting interval-block projections—replacing them by CRT-independent coordinates
   collapses back to the rejected Boolean/ANOVA model;
3. test the one-prime restriction, where no universal sign is available;
4. verify that any claimed square uses the tied clock `t=2pi/L`; an all-frequency square is
   impossible because the sine response is odd in `t`.

## Exact infinite block--Gamma sewing law

The Gamma operator in AES is no longer a representational guess.  Let `V_m=A_m^*` and let
`e_0` be the initial edge.  The normalized initial block seed `V_m e_0` is constant with value
`m^(-1/2)` on `[0,m)`.  Hence, for positive integers `m,n`,

```text
<V_m e_0,V_n e_0>
 =min(m,n)/sqrt(mn)
 =exp(-|log m-log n|/2).                                (AS9)
```

Put `r(m,n)` equal to this overlap.  The complete tensor degrees congruent to one modulo four
have the exact resolvent

```text
sum_(j>=0) r(m,n)^(4j+1)
 =r(m,n)/(1-r(m,n)^4).                                  (AS10)
```

For `m != n`, substituting `(AS9)` into `(AS10)` gives

```text
sum_(j>=0) r(m,n)^(4j+1)
 =exp(-|log(m/n)|/2)/(1-exp(-2|log(m/n)|))
 =ccmPublishedArchimedeanDensity(|log(m/n)|).           (AS11)
```

Thus the literal CCM Gamma density is the infinite odd block-Fock resolvent of the same aligned
subdivision algebra that carries the prime clock.  This is an infinite source law, not a finite
rank model and not a scalar insertion of `C_Gamma(L)`.  It explains the otherwise isolated
half-integer Gamma ladder `2j+1/2`: these are exactly tensor degrees `4j+1` of the critical
square-root block overlap.

Equations `(AS9)--(AS11)` are formalized unconditionally in
`CCMFirstClockBlockSubdivisionTransfer.lean` as:

```text
criticalBlockSeedGram_eq_exp_logGap
oddBlockFockRadialSum_eq
oddBlockFockRadialSum_exp_eq_archimedeanDensity
oddBlockFock_of_seedGram_eq_archimedeanDensity
```

This closes hostile test 1 at carrier level: Gamma and prime terms now live in one source-defined
infinite block algebra.  It does **not** prove `(AS7)`.  The remaining endpoint is no longer
“find a Gamma carrier”; it is the exact Schur innovation sign after conditioning the degree-one
prime transfer against the full `4j+1` block-Fock tower.  If that innovation is nonnegative for
the distinguished coboundary, `(AS7)` and RH follow.  If its negative part survives identically
as the counter half-wave, AES is dead.

Polar completion makes this still sharper.  Writing `r=exp(-h/2)`, Lean proves

```text
ccmFirstClockContinuousSourceDensity(h)
 = [sum_(j>=0) r^(4j+1)-r] - r^(-1)
 = sum_(j>=1) r^(4j+1)-r^(-1).                          (AS12)
```

After midpoint reflection, the continuous budget is exactly the decrease of the higher
`5,9,13,...` block-Fock tail plus the increase of the reflected growing polar sector.  The
degree-one decaying sector cancels identically.  Consequently a grade-preserving Fock lift cannot
touch the prime clock, which lives in degree one.  The surviving operator is forced to be a
source-defined **four-grade codiagonal** (or its singular relative-graph closure) coupling degree
one to degrees `5,9,13,...`, together with the reflected `-1` polar boundary.  This is formalized
by:

```text
continuousSourceDensity_eq_oddBlockFockTail_sub_polar
continuousReflectionGap_eq_blockFockTail_add_polarReflection
```

This identifies the first-clock form of the existing four-unit CCM frontier without assuming its
transport: prove the singular four-grade codiagonal is contractive on the distinguished
von-Mangoldt block coboundary, or prove every source-admissible closure has a nonzero vertical
innovation.  A diagonal Fock sum, bounded completion, or scalar Schur correction is now excluded
by `(AS12)` and the corpus saturation theorems.

There is an exact positive defect identity behind the codiagonal.  Let

```text
x_r(j)=r^(2j+1/2),  j>=0.
```

For the backward shift `B` on the grade ladder,

```text
||x_r||^2=sum_(j>=0)r^(4j+1)=r/(1-r^4),
||B x_r||^2=sum_(j>=1)r^(4j+1),
||x_r||^2-||B x_r||^2=r.                                (AS13)
```

At `r=q^(-1/2)`, the defect in `(AS13)` is exactly the critical Mellin radial weight.  Therefore
the literal prime clock has the unconditional relative-defect form

```text
P(L,t)
 =sum_(q<=exp L) Lambda(q)
   [||x_(q^-1/2)||^2-||B x_(q^-1/2)||^2]
   sin(t log q).                                         (AS14)
```

Lean proves `(AS13)--(AS14)` algebraically as

```text
oddBlockFockRadialSum_sub_tail
criticalMellinAtomWeight_eq_vonMangoldt_mul_oddBlockFockDefect
ccmFirstClockPrimeSineMass_eq_oddBlockFockDefectTrace
pi_mul_ccmPublishedSourceSineCoefficient_eq_budget_add_oddBlockFockDefectTrace
```

Thus both terms of the RH-complete first clock are now coordinates of one infinite Gamma/block
shift: continuous midpoint reflection is higher-grade plus polar boundary energy, while every
prime-power atom is the degree-one shift defect.  Missing theorem is the sign of the
phase-weighted **relative** defect trace after the source-selected cross-prime closure.  Ordinary
contraction only proves the unphased defect nonnegative; it cannot be applied after multiplying by
the counter-half-wave sine.  Any claimed completion must show where cross-prime source incidence
changes that signed trace before scalarization.

## Exact LCM meet and cofinal-collapse verdict

The noncommuting block ranges recover the causal LCM ridge which scalar convolution erased.  A
sequence is constant on aligned `q`-blocks exactly when it may jump only at indices divisible by
`q`.  Therefore

```text
BlockConst(lcm(m,n))
 <-> BlockConst(m) and BlockConst(n).                    (AS15)
```

Indeed, an adjacency is a simultaneous `m`- and `n`-boundary exactly when it is an
`lcm(m,n)`-boundary.  In Hilbert language,

```text
Ran(V_m) intersection Ran(V_n)=Ran(V_lcm(m,n)).          (AS16)
```

This is the sought finite future-divisor connector: future insertion becomes an actual meet of
aligned block channels on the same edge sequence, so the physical profile is neither frozen nor
rescaled by hand.  It is not Dirichlet-convolution prime-face scalarization.

The cofinal test is decisive.  If a sequence belongs to every aligned block channel of size
`q>=2`, choose `q=k+2` at adjacency `k -> k+1`; this adjacency is not a `q`-boundary, so consecutive
values agree.  Hence

```text
intersection_(q>=2) BlockConst(q) = {constant sequences}. (AS17)
```

Inside `ell^2(N)`, `(AS17)` is the zero channel.  Thus an unrenormalized alternating-projection or
future-meet exhaustion annihilates the first-clock coboundary and cannot prove RH.  The finite LCM
mechanism is genuine, but its cofinal limit must be taken as a singular relative defect/graph,
not a strong Hilbert-space projection limit.  This matches—now for the explicit block carrier—the
corpus theorem that bounded complete postprocessing saturates or collapses.

Lean:

```text
isAlignedBlockConstant_lcm_iff
alignedBlockReplication_range_lcm_iff_inter
isAlignedBlockConstant_all_ge_two_iff_constant
alignedBlockReplication_range_all_ge_two_iff_constant
```

The remaining live construction is therefore exact and narrow: renormalize the finite LCM meets
by the block-Fock shift defect `(AS13)` before the zero strong limit, retain the phase and
von Mangoldt mark in the relative trace, and prove its continuous Gamma--polar boundary is the
positive reflection budget.  If every such source-compatible renormalization recreates a vertical
innovation, the block/AES route is dead; ordinary projection convergence is already closed.

## Hostile audit of scalar successors

Two tempting scalar exits are closed and must not be retried.

1. **Cutoff-flow no-crossing fails.**  The hard first-clock budget is continuous when a prime
   power enters because its phase is `sin(2pi)=0`, but its right derivative at entry is negative:

   ```text
   d/dL sin(2pi log(q)/L) at L=log(q) = -2pi/log(q).
   ```

   Continuity and the already-proved all-depth Gamma orientation therefore do not prevent a
   crossing.  The crossing derivative is a separate cosine moment.

2. **Central-binomial carry sewing cancels the divisor.**  With
   `kappa(x)=floor(2x)-2floor(x)`, one has

   ```text
   log binom(2M,M)=sum_q Lambda(q) kappa(M/q),
   Mellin(kappa)(s)=(2^s-2) zeta(s)/s.
   ```

   Pairing this positive carry with `-zeta'/zeta` cancels the zeta denominator and therefore
   deletes the off-critical divisor which the CCM transport must preserve.  The natural smooth
   Gamma interpolation also has no fixed positive discrepancy: already at the exact symbolic
   half-integer comparison its ratio is `16/(9*pi)<1`.  Scalar carry/Gamma duplication is not the
   missing transport.  Only the noncommuting overlap/innovation sector in `(AS9)--(AS11)` survives.
