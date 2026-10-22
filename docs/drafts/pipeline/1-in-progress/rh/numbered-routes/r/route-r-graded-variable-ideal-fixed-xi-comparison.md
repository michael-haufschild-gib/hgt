# Route R graded variable-ideal comparison to the fixed Xi conormal

- **ID:** `route-r-graded-variable-ideal-fixed-xi-comparison`
- **Stage:** 1 — in progress
- **Type:** CONJECTURE RESEARCH / RH-BEARING SOURCE PRODUCER
- **Status:** `[RAW COMPARISON FORMALIZED] [RESOLVED COEFFICIENT LANDING FORMALIZED] [PHYSICAL NONERASURE CLASSIFIED] [OPEN GLOBAL NONERASURE] [NOT RH]`
- **Parents:**
  - `route-r-source-positive-polarization-stokes-flatness.md`;
  - `../../../../3-formalized/new_scientific_knowledge/ccm/rational-adelic-prime-isotropy-relative-xi-chain-map.md`;
  - `../3-formalized/new_scientific_knowledge/ccm/rational-adelic-prime-isotropy-stokes-regulator.md`;
  - `../../../../5-failed/route-r-source-stokes-cartier-graded-det2-trivialization.md`.
- **Statement:** Construct the minimal grade-dependent pullback ideal on which reflected prime
  character transport lands in the fixed physical trace ideal, prove exact coefficient
  faithfulness and reflection classification, and isolate the remaining source theorem needed to
  carry the retained rational-adelic prime-isotropy class without erasure.

## Goal

The rational-adelic class `eta_p=(0,1)` is retained and has period-one Stokes regulator one.  Its
strict resolved Xi landing is the prime-localized boundary of the actual leading Xi conormal.  The
resolved frame has a positive parallel polarization for every centered rate.  The missing arrow is
not another resolved chain map: it must cross the essential first-trace ideal and land in the fixed
same-fibre physical Xi conormal without erasing the coefficient read by the source regulator.

This card constructs the largest unconditional variable-ideal comparison into that fixed target.
It does not assume that the comparison is faithful at every Xi zero.  Instead it proves the exact
half-grade on which faithfulness holds and identifies source nonerasure in both reflected
orientations as the sole RH-bearing theorem left after the construction.

## Gates

- [x] 0 → 1 in-progress: exact source-pure target, construction, and generalized-prime falsifier
- [x] internal Route-R and failed-mechanism audit
- [x] raw variable-ideal comparison and coefficient classification proved on paper
- [x] formalize the dependency-closed comparison and classification in Lean
- [x] construct coefficient-faithful source Stokes landing in explicit variable-ideal resolved
  frame and prove strict resolved-boundary reporter square
- [x] construct both fixed physical orientation maps and classify exact nonerasure half-grades
- [ ] prove global physical nonerasure of the retained rational-adelic class in both orientations
- [ ] deduce the fixed same-fibre Xi comparison and RH

## Fixed physical ideal and raw reflected character

Let `P` be the ordinary primes and let

```text
S = P -> C,
I = {a in S | sum_p |a_p| < infinity}.
```

`I` is the fixed first-trace ideal.  It is independent of a divisor, grade, or reflection
orientation.  Put

```text
F(p)   = p/(p+1)^2,
F_t(p) = p^t F(p),
C_t(a)(p) = p^(-2t) a(p).
```

The raw character comparison has the exact laws

```text
C_t(F_t) = F_(-t),
C_(-t) C_t = id.
```

For every real grade define the pullback ideal

```text
J_t = C_t^(-1)(I) = {a in S | C_t(a) in I}.
```

This is not a topology selected after seeing a zero.  It is one predeclared graded family over the
whole real character line.  By definition `C_t` maps `J_t` into the fixed ideal `I`, and the inverse
law shows that it induces a linear isomorphism

```text
bar C_t : S/J_t -> S/I.                                      (GV1)
```

Thus `(GV1)` is the maximal raw variable-ideal comparison into the fixed physical quotient: if a
linear raw multiplier is required to equal `C_t`, its source ideal cannot contain anything outside
`J_t` while still landing in `I`.

## Resolved coefficient line and exact faithfulness wall

Keep the coefficient before physical quotienting by the formal resolved extension

```text
E_t = J_t + C e_t,
q_t(a + c e_t) = [C_t(a) + c F_(-t)] in S/I.                 (GV2)
```

The retained rational-adelic boundary is represented by `e_t`; its source Stokes regulator is the
coefficient map `Reg_t(a+c e_t)=c`.  The comparison satisfies

```text
q_t(e_t) = [F_(-t)].                                        (GV3)
```

For `|t|<1`, already proved prime summability gives

```text
F_u in I <-> u<0.
```

Consequently

```text
q_t is coefficient-faithful on C e_t
  <-> [F_(-t)] != 0 in S/I
  <-> not (-t<0)
  <-> t<=0.                                                 (GV4)
```

At reflected grade `-t`, the same construction is coefficient-faithful exactly when `0<=t`.
Therefore

```text
q_t and q_(-t) are both coefficient-faithful
  <-> t=0.                                                  (GV5)
```

This is stronger than the earlier fixed-Hilbert obstruction.  A common Hilbert carrier fails
outside `|t|<1/2`; the pullback ideals construct the singular comparison throughout the full Xi
strip `|t|<1`.  What remains is precisely nonerasure of one distinguished coefficient, not
existence of an ambient comparison.

## Dependency-closed proof

For every prime `p>0`, real-power addition gives

```text
p^(-2t) p^t = p^(-t).
```

Multiplying by `F(p)` proves the first raw identity.  Applying the same identity to exponents
`2t` and `-2t` proves `C_(-t) C_t=id`.  The definition of `J_t` makes `C_t(J_t)` a subset of `I`.
Conversely, if `b in I`, then `C_(-t)b in J_t` because
`C_t(C_(-t)b)=b`.  Hence `(GV1)` is bijective.

In `(GV2)`, the ideal coordinate maps into `I`, so the quotient landing is well-defined and equals
`c[F_(-t)]`.  Thus the coefficient line has zero kernel exactly when `[F_(-t)]` is nonzero.  In
the strip, the formalized Fisher summability classification says this is equivalent to
`not (-t<0)`, namely `t<=0`.  Replacing `t` by `-t` proves the reflected condition; their
conjunction is `t=0`.

No Xi zero, critical-line hypothesis, norm-conservative action, or post-selected topology occurs
in this proof.

## Constructed source and physical comparisons

For every ordinary prime `p` and actual Xi divisor copy `rho`, let

```text
c_rho = XiC^(m_rho)(rho) != 0,
t_rho = 2 Re(rho)-1.
```

The period-one Stokes regulator `Reg_p : H1_p -> C` now gives the explicit variable-ideal resolved
frame map

```text
S_(p,rho) : H1_p -> J_(t_rho) x C,
S_(p,rho)(x) = (0, Reg_p(x) c_rho).                        (GV6)
```

On the retained rational-adelic class `eta_p`, `Reg_p(eta_p)=1`, so

```text
S_(p,rho)(eta_p) = (0,c_rho) != 0.                         (GV7)
```

This is unconditional coefficient faithfulness before physical quotienting.  Its coefficient
reporter equals the second coordinate of the already constructed strict positive-resolved Xi
boundary at the depth-zero/depth-one cells over `p`; hence `(GV6)` is not a detached scalar model.
It carries the exact prime-localized, multiplicity-leading Xi conormal coefficient.

Physical specialization is

```text
P_t(a,c) = c [F_(-t)] in S/I.                              (GV8)
```

The composite `P_(t_rho) S_(p,rho)` is the constructed fixed same-fibre physical comparison.  It
sends the retained class to

```text
c_rho [F_(-t_rho)].                                        (GV9)
```

The Gamma-reflected construction sends it to `c_rho [F_(t_rho)]`.  Since `c_rho!=0`, the first
physical landing is nonzero exactly when `t_rho<=0`, and the reflected landing is nonzero exactly
when `0<=t_rho`.  Both are nonzero exactly when `Re(rho)=1/2`.  Globally, simultaneous physical
coefficient faithfulness is formally proved equivalent to RH.  Crucially, neither map nor the
resolved nonzero landing assumes that global property.

## Actual Xi consequence and exact open core

For an actual divisor copy `rho`, put

```text
t_rho = 2 Re(rho)-1.
```

The critical strip proves `|t_rho|<1`.  The functional equation supplies the reflected divisor
copy with grade `-t_rho`.  Hence a source-first theorem carrying the two retained, Stokes-normalized
rational-adelic classes through `(GV2)` without coefficient erasure forces `t_rho<=0` and
`-t_rho<=0`, so `t_rho=0`.

`[OPEN CORE] [RATIONAL_ADELIC_STOKES_FIXED_IDEAL_GLOBAL_NONERASURE]`

> Prove from pre-divisor rational-adelic/Gamma source structure that both constructed physical
> maps `(GV8)` retain `(GV7)` at every actual Xi divisor.  Map construction, exact leading-jet
> landing, strict resolved reporter compatibility, both Gamma orientations, and their complete
> nonerasure classification are finished.  Global nonerasure may not be inserted as a target
> axiom, inferred from criticality, or obtained by pulling a norm back through `(GV8)`; it must be
> a source theorem that fails on off-line generalized-prime carriers.

The existing norm-conservative source-character selector is the consumer after this theorem, not
the producer.  Calling `q_t` norm-conservative or coefficient-faithful by definition would assume
the conclusion.

## Hostile falsifiers

1. **Variable norm by decree.**  Giving `E_t` a norm pulled back through `q_t` makes every grade
   isometric and erases `(GV4)`; it is not the fixed physical ideal.
2. **Formal coefficient is not physical retention.**  `e_t` is always nonzero in the resolved
   extension.  Its image in `S/I` can vanish.  Treating formal nonzero as quotient nonzero is the
   precise invalid step this construction exposes.
3. **Reflection reciprocity is insufficient.**  `C_(-t)C_t=id` holds for every `t`.  Only
   simultaneous coefficient nonerasure in the fixed ideal is selective.
4. **Scalar conormal metric is insufficient.**  Top-conormal renormalization cancels its leading
   coefficient at every zero and sees no ideal-extension class.
5. **Resolved Stokes exactness is insufficient.**  The strict chain map lands on a resolved
   boundary for every `t`; ordinary target `H1` kills it.  The period-one regulator is secondary
   data and must be transported through `(GV2)`.
6. **Generalized-prime model.**  Any off-line generalized-prime carrier can support the raw family
   `(GV1)`.  It must fail clause (5) of the open core in one reflection orientation.  A proposed
   proof that works unchanged there is nonselective.

## No-go closure of superseded mechanisms

- **Exact killing theorem/mechanism:** fixed Hilbert completion, scalar Cartier metric,
  reflection-hyperbolic determinant balance, and ordinary chain homology all erase or symmetrize
  the coefficient needed by `(GV4)`.
- **Strongest positive survivor:** unconditional pullback-ideal comparison `(GV1)`--`(GV3)` and
  exact two-orientation coefficient-faithfulness classification `(GV4)`--`(GV5)`.
- **New insight:** singular comparison itself is not missing.  It exists canonically on a
  grade-dependent pullback ideal throughout the Xi strip.  Missing scientific knowledge is the
  source-derived theorem identifying the retained period-one Stokes coefficient with a nonzero
  class in the fixed physical ideal quotient in both Gamma orientations.
- **Status:** raw quotient equivalence, actual source Stokes map, resolved-frame coefficient
  faithfulness, strict reporter square, fixed physical specialization, reflection, local sign
  classification, and global RH equivalence are formalized unconditionally in
  `PrimeFirstTraceGradedVariableIdealFixedXiComparison.lean`; global source-derived physical
  nonerasure remains open.

## Log

- 2026-08-04 — Constructed maximal pullback ideal and raw comparison; proved exact coefficient
  wall and reflection classification.  Replaced overstrong full same-fibre unitary dagger by the
  minimal source-to-fixed-ideal nonerasure theorem.
