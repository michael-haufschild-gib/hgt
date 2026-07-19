# Weighted cubic Möbius innovation law and reflected strip no-go

- **ID:** `mobius-dyadic-cubic-reflection-aperture-no-go`
- **Stage:** 3-formalized/not_new_scientific_knowledge
- **Type:** THEOREM (Lean) / GENERAL WEIGHTED LIMIT / VALUE-REFLECTION CUBIC NO-GO
- **Scientific status:** `[PROVED] [FORMALIZED]
  [NOT NEW SCIENTIFIC KNOWLEDGE] [NOT AN RH PROOF]`
- **Lean:**
  `formal/GaloisForLFunctions/RHTower/XiMobiusDyadicCubicReflectionApertureNoGo.lean`
- **Parents:**
  - `../needs-audit/xi-mobius-continuous-aperture-szego-metric.md`
  - `mobius-continuous-aperture-tangent-rational-hurwitz-no-go.md`
  - `prime-seam-damping-aperture-law.md`
  - `uniform-positive-multiplier-summability-transfer.md`
- **Statement:** The primewise cubic dyadic source innovation admits one general all-prime
  dominated-convergence law for every nonnegative value weight with summable cubic source slope.
  It gives the previously open unweighted all-prime cubic curvature limit.  Applied to the
  normalized rational-Hurwitz reflection weight, it yields the third logarithmic moment of the
  unit-damped seam, hence the same exact open-strip classification and an unconditional cubic
  reflected germ limit on every Xi fibre.

## Primewise cubic coefficient and domination

For a prime `p`, put `q=p^(-1)`, `L=log p`, `d=q/(1+q)`, and let `I_p(h;a,b)` be the dyadic
innovation

```text
I_p(h;a,b)=2K_p(ha/2,hb/2)-K_p(ha,hb),                 (1)
```

where `K_p` is the continuous Möbius--Szego source metric.  The existing primewise theorem gives,
for `a,b>0`,

```text
I_p(h;a,b)/h^3 -> C_p(a,b),                            (2)

C_p(a,b)
 =d^2 ((aL/2)^2 (bL/2)^2)/((a+b)L)
 =[a^2 b^2/(16(a+b))] d^2 L^3.                        (3)
```

Define the cubic source slope `S_p=d^2L^3`.  It is summable because `0<d<=q` and
`sum_p (log p)^3/p^2<infinity`.

The exact positive Szego form of `(1)` is

```text
I_p=d^2 (1-r)^2(1-s)^2/[1-(rs)^2],                    (4)
```

with `r=exp(-haL/2)` and `s=exp(-hbL/2)`.  Since

```text
1-r <= haL/2,   1-s <= hbL/2,
1-(rs)^2 >= 1-r,                                      (5)
```

we obtain the uniform cubic bound

```text
0 <= I_p(h;a,b)/h^3 <= (a b^2/8) S_p.                 (6)
```

The asymmetric constant is harmless and keeps the proof elementary; swapping `a,b` gives the
companion bound.

## General weighted all-prime law

Let `w_p>=0` and assume `sum_p S_p w_p<infinity`.  Multiplying `(2)` and `(6)` by `w_p` and applying
dominated convergence gives the general law

```text
lim_(h->0+) [sum_p I_p(h;a,b)w_p]/h^3
  =sum_p C_p(a,b)w_p.                                  (7)
```

This theorem subsumes two previously separate interfaces.

First, `w_p=1` is admissible because `sum_p S_p<infinity`, so

```text
lim_(h->0+) I(h;a,b)/h^3=sum_p C_p(a,b).               (8)
```

This closes the unformalized all-prime cubic curvature limit on the continuous source-metric card.

Second, take `w_p=H_p(rho)`, the normalized rational-Hurwitz reflection energy.  The reflected
cubic coefficient `R_p(a,b;rho)=C_p(a,b)H_p(rho)` factors exactly as

```text
R_p(a,b;rho)
 =[a^2 b^2/(64(a+b))] * 1/(1+q)^2
   * L^3 p^(-1)(p^(-sigma)-p^(-(1-sigma)))^2.          (9)
```

The local multiplier in front of the third log moment is bounded between one quarter and one times
the positive constant `a^2b^2/[64(a+b)]`.  Therefore

```text
sum_p R_p(a,b;rho)<infinity
  iff sigma=1/2 or |2sigma-1|<1.                       (10)
```

On the open strip, `(10)` also makes `sum_p S_pH_p(rho)` finite.  Applying `(7)` yields the actual
reflected cubic germ

```text
lim_(h->0+) [sum_p I_p(h;a,b)H_p(rho)]/h^3
  =sum_p R_p(a,b;rho).                                 (11)
```

Every Xi zero lies in the open strip unconditionally, so both `(10)` and `(11)` hold on every Xi
fibre without RH.

## No-go closure and positive successor

- **Exact killing mechanism:** the first dyadic refinement curvature inserts the third fixed
  logarithmic moment but leaves the reciprocal-prime power damping unchanged.  It cannot alter the
  prime-zeta convergence wall.
- **Strongest positive survivor:** the arbitrary nonnegative weighted limit `(7)`, the unweighted
  all-prime cubic source law `(8)`, the exact reflected classification `(10)`, and the all-Xi cubic
  germ `(11)`.
- **New insight:** both the first tangent and the first nonlinear dyadic curvature are finite across
  the whole critical strip.  Finite-order aperture differentiation/refinement is not by itself an
  RH selector; any surviving route must supply sign-sensitive contractivity, change the prime-power
  loss cofinally, or use a genuinely non-finite-order boundary effect.
- **Status:** dependency-closed paper proof and exact Lean formalization.  The source check, exact
  Lake target build, and representative axiom audit pass.

## Novelty and parent boundary

The exponential-gap estimates, logarithmically weighted inverse-square summability, and dominated
convergence are classical.  The weighted abstraction and its source/value specializations close
project-internal theorem interfaces.  No standalone new-science claim is made.

## Gates

- [x] primewise cubic coefficient and positivity already proved in the corpus
- [x] uniform cubic domination proved on paper
- [x] general nonnegative weighted all-prime limit proved on paper
- [x] unweighted all-prime cubic source limit proved on paper
- [x] reflected cubic factorization and exact aperture proved on paper
- [x] reflected cubic germ and all-Xi consequences proved on paper
- [x] formalize the weighted law and both specializations
- [ ] derive source contractivity or an exponent-changing/non-finite-order law

## Log

- 2026-07-19 — extracted from the open all-prime cubic-curvature gate after the first reflected
  source tangent was classified.  The key simplification is the denominator bound
  `1-(rs)^2>=1-r`, which gives a prime-uniform cubic majorant without a small-`h log p` restriction.
- 2026-07-19 — formalized the cubic slope summability and domination, arbitrary nonnegative
  weighted limit, unweighted all-prime source limit, exact reflected third-moment splice and
  aperture, reflected cubic germ, and two all-positive-aperture-pair Xi Props.  The exact leaf
  source check and target build pass; representative declarations use only `propext`,
  `Classical.choice`, and `Quot.sound`.
