# The actual Euler Mertens class is a rank-one shift conormal

- **ID:** `mertens-corona-shift-conormal`
- **Stage:** 2-fully-proven/not_new_scientific_knowledge
- **Type:** THEOREM (paper) / SOURCE CONORMAL / MACKEY-CORONA BRIDGE
- **Scientific status:** `[PROVED HERE] [NOT FORMALIZED]
  [NOT NEW SCIENTIFIC KNOWLEDGE] [NOT AN RH PROOF]`
- **Parents:**
  - `../new_scientific_knowledge/weighted-euler-tangent-global-graph-decoupling.md`
  - `gamma-meixner-abel-mertens-corona-probe.md`
  - `../../1-in-progress/hypertranscendental-mackey-corona-field.md`
- **Statement:** On the actual Euler coefficient space `C one+M_0`, coefficient of the unit
  Mertens class is a canonical continuous conormal.  Prime unit translation sends the whole space
  into `M_0`, so the conormal is killed by the translated source and detects the complete shift
  defect.  Gamma--Meixner Abel probes converge to it, and the time-one prime--Laplace boundary
  residue is its analytic realization.

## The actual-source coefficient space

Let `M_log` be the logarithmic Marcinkiewicz prime-field space and `M_0` its closed
finite-support/vanishing-tail subspace.  The actual unit field

```text
one_p=1                                                   (1)
```

belongs to `M_log` but not `M_0`, and its quotient class has norm one.  Put

```text
E_actual=C one+M_0.                                      (2)
```

Because `one notin M_0`, every `x in E_actual` has a unique decomposition

```text
x=c one+b,       c in C, b in M_0.                       (3)
```

Define

```text
q_M(x)=c.                                                 (4)
```

Then `q_M` is the unique linear functional on `E_actual` satisfying

```text
q_M(one)=1,
q_M|M_0=0.                                               (5)
```

It is continuous in the inherited Marcinkiewicz topology.  Indeed, the quotient map gives

```text
||[x]||=|c| ||[one]||=|c|<=||x||_M.                      (6)
```

Thus `(4)` is not a weak-star cluster choice: it is the canonical coordinate of the actual affine
source on its one-dimensional quotient line.

## Exact shift-conormal law

Define prime unit translation

```text
(S b)_p=p^(-1)b_p.                                       (7)
```

It is bounded on `M_log`, since `p^(-1)<=1/2`, and preserves `M_0` by continuity from finite
support.  Moreover

```text
S one=(p |-> p^(-1)) in T_1 subset M_0.                  (8)
```

Therefore

```text
S(E_actual) subset M_0,
q_M S=0.                                                 (9)
```

For the source defect `D=I-S`, equations `(5)` and `(9)` give

```text
q_M D=q_M.                                               (10)
```

Thus `C q_M` is a cyclic rank-one module for the dual shift action: translation annihilates the
corona conormal, while the complete unit-translation defect is detected with eigenvalue one.
This is the coefficient-level corona conormal and transgression predicted by the
Mackey--corona field.

## Gamma--Meixner Abel realization

The normalized Gamma-shape functionals

```text
L_theta(b)
 =theta sum_p (log p)/p w_theta(p)b_p                    (11)
```

satisfy

```text
L_theta(b)->0       for b in M_0,
L_theta(one)->1.                                          (12)
```

Consequently, for every `x=c one+b` in `E_actual`,

```text
L_theta(x)->c=q_M(x).                                    (13)
```

The Abel family therefore converges pointwise on the complete actual-source affine space to the
canonical conormal `(4)`.  Weak-star nonuniqueness on the rest of `M_log/M_0` is irrelevant to
this one-dimensional source line.

## Time-one boundary residue

For `b in E_actual`, put

```text
M_(1,b)(s)=sum_p w_1(p)(log p)b_p p^(-s).                (14)
```

The exact time-one weight has leading form `sqrt(2)p^(-1)`.  The Abel theorem and the absolutely
summable `O(p^(-5))` correction give

```text
lim_(s down to 0) s M_(1,b)(s)=sqrt(2) q_M(b).           (15)
```

Thus the simple pole of the time-one prime--Laplace source is exactly the analytic residue of the
Mertens conormal.  For the reflected pair, its translated polar doublet is

```text
sqrt(2)q_M(one)
 [1/(z+rho)-1/(z+1-conjugate(rho))].                     (16)
```

The RH support selector is therefore the reflected transgression of the concrete rank-one
conormal `(4)`, not an unspecified corona character.

## Exact factorial boundary transgression

Represent the conormal class `c q_M` by its polar germ

```text
r_c(z)=sqrt(2)c/z.                                       (17)
```

At any fixed `x_0>1`, its `N`-th raw derivative is

```text
r_c^(N)(x_0)
 =sqrt(2)c(-1)^N N!/x_0^(N+1).                          (18)
```

Let `jet_(N+1)(r_c)` be the first `N+1` raw derivatives and let `kappa_N` be Gamma's
adjacent-clock curvature.  The formalized rank-one formula gives

```text
kappa_N(jet_(N+1)(r_c))
 =r_c^(N)(x_0) beta_N,                                  (19)

beta_N(i)=1/(N-i)!.                                     (20)
```

For `c!=0`, the scalar `(18)` is nonzero at every resolution.  Hence the Mertens conormal has:

```text
one source-operator generator,
rank-one boundary symbol,
nonzero transgression at every clock layer.              (21)
```

This proves the tail-faithful thin-current law for the coefficient polar quotient.  The
factorial boundary vector was not matched by rank counting; it is the exact curvature image of
the analytic residue germ.

## Product-topology no-go and positive successor

Finite-support fields are product-dense, so `q_M` is not continuous in the raw product clock.
This is exactly the Lean-formalized topology necessity theorem: a nonzero Hausdorff conormal
annihilating a finite-observably free tangent forces a strict minimal refinement.

The nontrivial positive successor is now explicit:

1. the coefficient source space is `E_actual`;
2. the conormal is `q_M`;
3. its shift module is rank one with law `(9)`;
4. its analytic Abel realization is `(13)`;
5. its time-one boundary residue is `(15)`.
6. its tail-faithful Gamma boundary transgression is `(19)`.

The remaining RH theorem is not to construct a coefficient corona or its polar transgression from
nothing.  It is to extend `C q_M` and `(19)` from the coefficient polar quotient to the intrinsic
completed Euler--Gamma source-operator conormal and prove affine support preservation in the
calibrated zero-orbit comparison.

## Parent-theory boundary

One-dimensional quotients, bounded diagonal shifts, Abel limits, and residue extraction are
classical.  This is a project bridge and is not claimed as new scientific knowledge.  Candidate
new content begins with the full source-operator extension and its framed Gamma transgression.

## Gates

- [x] actual-source quotient line isolated
- [x] unique continuous Mertens conormal constructed
- [x] exact dual shift-annihilation law proved
- [x] Gamma--Meixner Abel convergence to the conormal proved
- [x] time-one boundary residue identified
- [x] tail-faithful rank-one Gamma transgression identified on the polar quotient
- [x] product-topology no-go given an explicit positive source object
- [ ] extend to the completed Euler--Gamma source operator algebra
- [ ] lift the polar transgression to the full framed source comparison
- [ ] prove calibrated zero-orbit affine-support preservation
