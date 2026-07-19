# Fixed continuous Möbius apertures all see the same critical strip

- **ID:** `mobius-continuous-aperture-rational-hurwitz-no-go`
- **Stage:** 3-formalized/not_new_scientific_knowledge
- **Type:** THEOREM (Lean) / APERTURE-FAMILY CLASSIFICATION / NO-GO WITH POSITIVE SUCCESSOR
- **Scientific status:** `[PROVED] [FORMALIZED]
  [NOT NEW SCIENTIFIC KNOWLEDGE] [NOT AN RH PROOF]`
- **Lean:**
  `formal/GaloisForLFunctions/RHTower/XiMobiusContinuousApertureRationalHurwitzNoGo.lean`
- **Parents:**
  - `../needs-audit/xi-mobius-continuous-aperture-szego-metric.md`
  - `mobius-schur-rational-hurwitz-lorentz-aperture.md`
  - `prime-seam-damping-aperture-law.md`
  - `uniform-positive-multiplier-summability-transfer.md`
- **Statement:** For every fixed real source aperture `a>0`, the diagonal continuous
  Möbius--Szego metric applied to the normalized rational-Hurwitz reflection energy is summable
  exactly on the open critical strip, with the critical line as the identically zero case.  The
  classification is independent of `a`; hence varying a fixed positive aperture cannot strengthen
  Hilbert membership into RH.

## Exact source/value splice

For a prime `p`, put

```text
q=p^(-1),   r_a=p^(-a),
M_a(p)=(q/(1+q))^2 (1-r_a)/(1+r_a).                    (1)
```

Here `M_a(p)` is the diagonal of the continuous Möbius--Szego source metric.  If
`rho=sigma+i*t`, the normalized rational-Hurwitz reflection energy is

```text
H_p(rho)=p/4 (p^(-sigma)-p^(-(1-sigma)))^2.             (2)
```

Writing `A_p(sigma)=p^(-sigma)-p^(-(1-sigma))`, multiplication gives

```text
M_a(p) H_p(rho)
 = F_a(p) p^(-1) A_p(sigma)^2,                          (3)

F_a(p)=1/[4(1+q)^2] * (1-r_a)/(1+r_a).                 (4)
```

At `a=1`, `(1)` is exactly the previously constructed Möbius Schur difference-kernel diagonal,
so `(3)` genuinely extends the unit-aperture source/value bridge rather than introducing a second
unrelated metric.

## Uniform comparison for each fixed aperture

Fix `a>0` and let `R_a=exp(-a log 2)`.  Since every prime is at least two,

```text
0<q<1,   0<r_a<=R_a<1.                                 (5)
```

Consequently

```text
1/(1+q)^2 >= 1/4,
(1-r_a)/(1+r_a) >= (1-R_a)/2.                           (6)
```

The second inequality follows by first decreasing the numerator from `1-r_a` to `1-R_a` and
then increasing the positive denominator from `1+r_a` to `2`.  Therefore

```text
c_a := (1-R_a)/32 > 0,
c_a <= F_a(p) <= 1                                     (7)
```

for every prime `p`.  The lower constant depends on `a`, but not on `p`.  Equations `(3)` and `(7)`
show that, for each fixed positive aperture, the continuous source energy and the unit-damped
prime-clock reflection energy are two-sided comparable nonnegative prime series.

## Exact fixed-aperture classification

The general prime-seam damping law at damping exponent one now gives, for every fixed `a>0`,

```text
sum_p M_a(p) H_p(rho)<infinity
  iff sum_p p^(-1) A_p(sigma)^2<infinity
  iff sigma=1/2 or |2sigma-1|<1.                        (8)
```

Every Xi zero lies in `0<sigma<1` unconditionally.  Hence the quantified proposition

```text
for every a>0 and every rho,
  xi(rho)=0 -> sum_p M_a(p) H_p(rho)<infinity            (9)
```

is itself unconditional, not an RH criterion.

## No-go closure and positive successor

- **Exact killing mechanism:** every fixed `a>0` changes the source diagonal only by a primewise
  factor bounded above and below by positive constants.  Such a change cannot alter the unit
  damping summability threshold.
- **Strongest positive survivor:** the entire positive continuous-aperture family has the exact
  aperture classification `(8)`, and all of its fixed-aperture Xi-fibre membership Props discharge
  unconditionally.
- **New insight:** the fixed-aperture lower comparison degenerates at `a -> 0+`, but the first
  renormalized source germ has now also been classified: it inserts one logarithmic moment and
  remains finite throughout the critical strip.  The exact remaining interface is therefore a
  source-built contraction/passivity estimate, an exponent-changing cofinal loss law, a
  non-finite-order boundary effect, or equivalent signed trace cancellation.
- **Status:** dependency-closed paper proof and exact Lean formalization.  The source check, exact
  Lake target build, and representative axiom audit pass.

## Novelty and parent boundary

The comparison of positive series under bounded weights and the prime-zeta convergence threshold
are classical.  The theorem closes a project-internal compatibility gap between the continuous
Möbius source metric and the rational-Hurwitz value-reflection energy.  No standalone new-science
claim is made.

## Gates

- [x] existing continuous source metric and unit reflection bridge audited
- [x] exact continuous source/value factorization derived
- [x] unit aperture identified with the canonical Möbius Schur metric
- [x] fixed-aperture two-sided comparison proved on paper
- [x] exact summability classification and unconditional Xi consequence proved on paper
- [x] fixed-aperture tuning route retired with a positive survivor
- [x] formalize the splice, comparison, classification, and quantified Prop discharge
- [x] classify the first normalized `a -> 0+` value-reflection germ
- [ ] derive source contractivity or a genuinely exponent-changing cofinal law

## Log

- 2026-07-19 — extracted after the unit Möbius/Lorentz aperture classification.  A corpus search
  found the continuous source metric and its prime-square upper bound, but no theorem connecting it
  to rational-Hurwitz reflections or classifying its exact summability aperture.
- 2026-07-19 — formalized prime-antitonicity of the continuous disk node, the exact aperture-one
  identification, the continuous source/value splice, fixed-aperture two-sided comparison, exact
  summability classification, and unconditional all-positive-aperture Xi Prop.  The exact leaf
  source check and target build pass; representative declarations use only `propext`,
  `Classical.choice`, and `Quot.sound`.
- 2026-07-19 — the first zero-aperture tangent escape was subsequently closed by
  `mobius-continuous-aperture-tangent-rational-hurwitz-no-go.md`: its normalized total germ exists
  and is finite on every Xi fibre unconditionally.
