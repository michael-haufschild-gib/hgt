# Finite commuting shifts peel differential algebraicity down to rationality

- **ID:** `finite-commuting-shift-peeling-hypertranscendence-law`
- **Stage:** 2-fully-proven / paper proof complete
- **Type:** THEOREM (paper) / GENERAL HYPERTRANSCENDENCE LANDSCAPE
- **Scientific status:** `[PROVED] [BRIDGE]`
- **Statement:** Let `f in C((s^(-1)))`. If a finite product of nonzero constant-shift differences
  sends `f` to a rational function, then `f` is rational or hypertranscendental over `C(s)`. Thus a
  differentially algebraic Laurent-series solution is forced to carry a rational representative,
  even when the shifts are mutually incommensurable.

## 1. One-shift inhomogeneous lemma

For `h in C^x`, write

```text
rho_h f(s)=f(s+h),
Delta_h=rho_h-1.                                           (1)
```

`[PROVED FROM ADAMCZEWSKI--DREYFUS--HARDOUIN]` If

```text
f in C((s^(-1))),
Delta_h f=r in C(s),                                       (2)
```

then

```text
f in C(s) or f is HT over C(s).                            (3)
```

### Proof

If `r=0`, then `f(s+h)=f(s)`. Comparing the first nonconstant Laurent monomial with its translate
shows that a periodic formal Laurent series is constant, hence rational.

Assume `r!=0` and put

```text
q=rho_h(r)/r in C(s)^x.                                    (4)
```

Equation `(2)` implies the homogeneous rational shift equation

```text
(rho_h-q)(rho_h-1)f=0.                                     (5)
```

Adamczewski--Dreyfus--Hardouin, Theorem 1.2 in Case `S_infinity`, says that a Laurent-series
solution of a homogeneous rational linear shift equation is rational or hypertranscendental. This
gives `(3)`.

## 2. Finite commuting-shift peeling theorem

Fix arbitrary nonzero shifts `h_1,...,h_d in C^x`; no commensurability is assumed.

`[PROVED]` If

```text
Delta_(h_1)...Delta_(h_d) f in C(s),                       (6)
```

then `f` is rational or hypertranscendental over `C(s)`.

### Proof

Suppose `f` is differentially algebraic. Affine translation preserves differential algebraicity,
so every finite difference of `f` is DA. Put

```text
g_1=Delta_(h_2)...Delta_(h_d)f.                            (7)
```

Then `Delta_(h_1)g_1` is rational by `(6)`. The one-shift lemma forces `g_1` to be rational. Next put

```text
g_2=Delta_(h_3)...Delta_(h_d)f.                            (8)
```

It is DA and satisfies `Delta_(h_2)g_2=g_1 in C(s)`, so the one-shift lemma makes `g_2` rational.
Continue. After `d` steps, `f` itself is rational. Therefore every nonrational `f` satisfying `(6)`
is HT.

The shifts commute because they are translations, but the proof uses no common generator and no
rational relation among them.

## 3. Positive constraint law

The theorem identifies a forced carrier:

> **Finite-shift rational-carrier law.** A Laurent-series object constrained by finitely many
> commuting additive differences and by differential algebraicity must descend through every
> difference layer to the rational base field. Incommensurability creates no DA escape channel.

Equivalently, the product of difference operators may be peeled as a finite constraint hierarchy:

```text
multi-shift rational source
 -> one fewer shift with rational source
 -> ...
 -> rational Laurent-series carrier.                      (9)
```

This is a constraint-side argument, not a flow: no shift is selected as a common time parameter.

## 4. Attacks and exact scope

1. **The Laurent-series ambient field is load-bearing.** Global meromorphic one-shift equations can
   have DA periodic and exponential solutions. The `S_infinity` Laurent field excludes them.
2. **The source must be rational at the first layer.** If `(6)` merely lands in an arbitrary DA
   field, the one-shift theorem does not force rationality.
3. **Finitely many shifts are load-bearing.** An infinite product cannot be peeled in finitely many
   applications of the one-shift theorem.
4. **Commensurability is irrelevant.** Repeated shifts may coincide or be rationally independent;
   the induction is unchanged.
5. **The theorem does not classify rationality.** A separate residue or summability invariant must
   decide whether the rational branch occurs.

## 5. Parent and novelty audit

`[BRIDGE]` The one-shift dichotomy is Adamczewski--Dreyfus--Hardouin. The many-shift statement is a
finite induction after observing that translations preserve differential algebraicity. It is useful
but fails the parent-theory gate for new scientific knowledge.

Primary source:

- B. Adamczewski, T. Dreyfus, C. Hardouin, *Hypertranscendence and linear difference equations*,
  J. Amer. Math. Soc. 34 (2021), 475--503, Theorem 1.2, Case `S_infinity`.

## 6. Lean status

The tree has elementary translation/difference algebra, `trigamma_recurrence`, and a common-shift
finite-pole obstruction, but no formal Laurent-series shift theorem or formal HT interface
implementing the cited dichotomy. The complete claim is not formalized and remains stage 2.

## Gates

- [x] one-shift inhomogeneous lemma derived
- [x] arbitrary finite shifts peeled inductively
- [x] commensurability removed
- [x] positive rational-carrier law stated
- [x] edge cases attacked
- [x] parent-theory gate applied; classified BRIDGE
- [ ] complete unconditional Lean formalization
