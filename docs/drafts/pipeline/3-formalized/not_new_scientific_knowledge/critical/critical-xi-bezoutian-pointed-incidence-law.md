# The critical Xi Bezoutian is the pointed global incidence kernel for the Connes route

- **ID:** `critical-xi-bezoutian-pointed-incidence-law`
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean), `[BRIDGE]`
- **Scientific status:** `[PROVED HERE] [NOT NEW SCIENTIFIC KNOWLEDGE] [NOT AN RH PROOF]`
- **Parent results:** the critical log-derivative Pick kernel, the polarized Weil form, and the
  theta-source realization of Xi
- **Statement:** Clearing the completed logarithmic derivative by the actual Xi trace produces an
  entire two-variable Bezoutian. Its positivity on the Euler half-plane is equivalent to RH, it is
  exactly the completed two-channel Weil resolvent Gram, and it is determined by the pointed
  theta/Euler/trace-moment source rather than by a local regular germ.

## Entire Bezoutian

Put

```text
X(w)=xi(1/2+w).                                            (1)
```

Then `X` is even, entire, real under conjugation, and `X(0)!=0`. Define

```text
B_X(w,v)
 =(X'(w)conjugate(X(v))+X(w)conjugate(X'(v)))
   /(w+conjugate(v)).                                      (2)
```

Although `(2)` is written as a quotient, it extends holomorphically in `w` and
antiholomorphically in `v` across `w+conjugate(v)=0`.

### Proof of removability

Write `y=conjugate(v)`. The numerator is

```text
N(w,y)=X'(w)X(y)+X(w)X'(y).                               (3)
```

On `y=-w`, evenness of `X` and oddness of `X'` give

```text
N(w,-w)=X'(w)X(w)-X(w)X'(w)=0.                            (4)
```

The entire function `N(w,y)` therefore vanishes on the irreducible hyperplane `w+y=0`, so it is
divisible by `w+y` in the ring of entire functions. The quotient is the entire extension of
`B_X`.

Equivalently,

```text
B_X(w,v)
 =X(w)conjugate(X(v))
   *(L(w)+conjugate(L(v)))/(w+conjugate(v)),               (5)

L=X'/X,                                                    (6)
```

wherever the displayed logarithmic derivatives are regular.

## RH equivalence on the Euler half-plane

The following are equivalent:

```text
(i)  RH;

(ii) B_X is a positive kernel on Re w>1/2;

(iii) for every finite node system w_j in Re w>1/2,
      (B_X(w_j,w_k))_(j,k)>=0.                             (7)
```

### Proof

The half-plane `Re w>1/2` corresponds to `Re(1/2+w)>1`, so `X` has no zeros there. Multiplication of
a finite Gram matrix by the invertible diagonal matrix

```text
diag(X(w_1),...,X(w_N))                                    (8)
```

is a congruence. Equation `(5)` therefore identifies positivity of the Bezoutian matrices with
positivity of the critical logarithmic-derivative matrices. The complete-detector theorem in
`critical-logderivative-two-channel-weil-resolvent-law.md` identifies the latter with RH. This
proves `(7)`.

## Completed two-channel Weil identity

For `Re w>1/2`, let

```text
A_w(alpha)=w/(w^2+alpha^2),
B_w(alpha)=alpha/(w^2+alpha^2).                            (9)
```

The two-channel theorem and `(5)` give

```text
B_X(w,v)
 =q_W(X(w)A_w,X(v)A_v)
  +q_W(X(w)B_w,X(v)B_v),                                  (10)
```

where scalar factors act in the node parameter and `q_W` is the polarized Weil source form. More
explicitly, using the centered divisor modulo sign,

```text
B_X(w,v)
 =sum_(alpha mod +-)
   2m_alpha X(w)conjugate(X(v))
   *(w conjugate(v)+alpha^2)
   /((w^2+alpha^2)(conjugate(v)^2+alpha^2)).               (11)
```

The apparent poles at `w=+-i alpha` are removable because `X` vanishes there. Under RH every
`alpha` is real, and `(11)` is the positive Gram sum of the two entire feature channels

```text
E_(alpha,0)(w)
 =sqrt(2m_alpha) X(w)w/(w^2+alpha^2),

E_(alpha,1)(w)
 =sqrt(2m_alpha) X(w)alpha/(w^2+alpha^2).                  (12)
```

Away from RH, `(10)` remains the unconditional polarized Weil identity, but the divisor pairing is
indefinite.

## Pointed source presentation

The kernel `(2)` has two simultaneous source presentations.

### Theta/trace presentation

Riemann's theta formula gives `X` as the completed Fourier--Mellin trace of the fixed positive theta
source. Differentiation gives `X'`. Hence `(2)` is determined by

```text
completed theta source
  + distinguished trace X
  + its full even-moment/odd-log-trace germ.                (13)
```

The exact odd-trace/even-moment inverse in `CriticalTraceMomentGerm.lean` makes the last clause an
invertible pointed coordinate, not a finite jet heuristic.

### Euler--Gamma presentation

On `Re w>1/2`,

```text
X'(w)/X(w)
 =b(1/2+w)
  -sum_(n>=2)Lambda(n)n^(-1/2-w),                          (14)
```

so `(5)` is determined by

```text
weighted all-prime coefficient tail
  + finite-degree archimedean completion
  + the same distinguished completed trace X.             (15)
```

Equations `(13)`--`(15)` are the pointed global incidence structure forced by the critical-disc
Euler-orbit quotient theorems. Compact-open regular-germ convergence alone forgets precisely the
data retained in `(13)`--`(15)`.

## Positive factorization target

The direct source theorem is now unambiguous:

```text
construct a Hilbert space H_src and source-defined vectors R_w in H_src
such that

B_X(w,v)=<R_v,R_w>_(H_src)
for Re w,Re v>1/2.                                        (16)
```

Compatibility under enlargement of finite node sets is part of `(16)`. By `(7)`, such a
factorization proves RH. Constructing `H_src` as the abstract RKHS of an already-assumed positive
`B_X`, or constructing `(12)` after listing real zeros, is target-fed and does not count.

The Hedenmalm metric classification sharpens the form of a valid construction. Any continuous
positive source-core form symmetrizing the theta differential pair is necessarily nonlocal and has
Fourier measure supported on the real Xi divisor; ordinary weighted `L2` and finite-order local
differential metrics are zero. Therefore a successful factorization `(16)` must be a genuinely
nonlocal all-prime rigging whose divisor support emerges from the source identity, not a local
Gamma metric.

## Signed-Gamma rank boundary

The neutral signed-Gamma theorem proves

```text
K_G
 ->C[z,e^(beta z),e^(-beta z)]
 ->C[e^(beta z),e^(-beta z)]                               (17)
```

and the recurrent bound

```text
rank_Q Gamma_B(f)<=delta_beta+2m(n+1).                     (18)
```

Consequently `(16)` must carry the complementary prime-character module of rank at least

```text
pi(N)-delta_beta-2m(n+1)                                  (19)
```

through cutoff `N`, unless its differential-state complexity grows accordingly. The theta trace
in `(13)` supplies completion and moments; it does not license the Gamma field to impersonate the
independent prime phases in `(15)`.

## Relation to CCM

The chain is now exact:

```text
source factorization of the entire Bezoutian B_X
  -> positive critical Euler resolvent matrices
  -> exponentially convergent even/odd aperture channels
  -> no negative compact screw mode at any aperture
  -> conserved zero Morse charge
  -> RH.                                                    (20)
```

This is the positive Connes--CCM architecture after all finite-determinant and fixed-source
shortcuts are removed.

## Scientific status

The Bezoutian identity, diagonal congruence, and zero-side feature expansion are standard
consequences of the logarithmic derivative and Weil polarization. Their assembly gives the correct
pointed source object but is classified as bridge infrastructure, not new scientific knowledge.

## References

- `critical-logderivative-two-channel-weil-resolvent-law.md`.
- `critical-euler-weighted-shift-accretivity-law.md`.
- `hedenmalm-pair-weil-polarization-law.md`.
- `hedenmalm-theta-pair-divisor-supported-metric-law.md`.
- `signed-archimedean-gamma-orbit-charge-phase-law.md`.

## Lean decision (SUPERSEDED)

The two-variable Bezoutian, the Weil distribution, and the Pick extension are now all in the tree,
so `(7)`, `(10)`–`(12)` and the source presentations are certified; see below.

## Gates

- [x] entire Xi Bezoutian constructed
- [x] removability proved
- [x] Euler-half-plane positivity proved equivalent to RH
- [x] completed two-channel Weil identity proved
- [x] theta/trace and Euler--Gamma source presentations identified
- [x] local-metric obstruction incorporated positively
- [x] signed-Gamma complementary rank bound incorporated
- [ ] construct the non-target-fed source Gram factorization `(16)`
- [ ] deduce RH


## Lean formalization — the proved content is COMPLETE (unconditional)

New module `RHTower/XiBezoutianPointedIncidence`, plus `isPSDKernel_gram` added to
`HTGeometry/PSDKernelOperations`.  Every capstone audits to
`propext, Classical.choice, Quot.sound`.

### The entire Bezoutian and its removability

| Card item | Lean name |
|---|---|
| `X` even, `X'` odd | `xiCent_even`, `deriv_xiCent_neg` |
| Schwarz reality of `X` and `X'` | `xiCent_conj`, `deriv_xiCent_conj` |
| `(3)` the numerator `N(w,y)` | `xiCentBezoutianNumerator` |
| **`(4)`** `N(w,-w) = 0` | `xiCentBezoutianNumerator_antidiagonal` |
| `(2)` the Bezoutian, defined across the antidiagonal | `xiCentBezoutian` (a `dslope`) |
| the quotient form off the antidiagonal | `xiCentBezoutian_eq_div` |
| **removability**: entire in the holomorphic variable | `differentiable_xiCentBezoutian` |
| agreement with the corpus value-fibre Bezoutian at `c = 0` | `xiCentBezoutian_eq_xiTranslatedBezoutian` |
| **`(5)`** `B_X = X(w) conj(X(v)) · K_L(w,v)` | `xiCentBezoutian_eq_mul_criticalKernel` |

### RH equivalence on the Euler half plane

| Card item | Lean name |
|---|---|
| **`(7)`** RH ⟺ every finite Bezoutian matrix on `Re w > 1/2` is positive semidefinite | `riemannHypothesis_iff_posSemidef_xiCentBezoutian` |

The proof is the card's: the diagonal congruence by `diag (X w_j)` (corpus
`posSemidef_congr_diagonal`) transports positivity between the Bezoutian matrices and the critical
logarithmic-derivative matrices, and the latter is
`riemannHypothesis_iff_isPSDKernel_criticalLogDerivKernel` from
`critical-logderivative-euler-safe-cauchy-loss-law`.  Note this is on the *Euler* half plane
`Re w > 1/2`; the corpus already had the coarser `Re w > 0` statement
(`posSemidef_xiTranslatedBezoutian_iff`).

### The completed two-channel Weil identity

| Card item | Lean name |
|---|---|
| **`(10)`** `B_X = q_W(X A_w, X A_v) + q_W(X B_w, X B_v)` | `xiCentBezoutian_eq_twoChannelWeil` |
| **`(11)`** the explicit divisor expansion | `xiCentBezoutian_eq_tsum` |
| `(12)` the entire feature channels | `xiFeatureChannelEven`, `xiFeatureChannelOdd` |
| **`(12)`** under RH the Bezoutian is their positive Gram sum | `xiCentBezoutian_eq_featureGram_of_riemannHypothesis` |

### The source presentations and the budget

| Card item | Lean name |
|---|---|
| `(14)`–`(15)` Euler--Gamma presentation | `logDeriv_xiCent_eq_eulerPresentation`, `lSeriesSummable_vonMangoldt_shift` (`RHTower/XiWeilTwoChannelResolvent`) |
| `(13)` theta/trace presentation: the invertible pointed odd-trace/even-moment coordinate | `normalizedTraceMomentGerm_criticalTraceToCenteredOdd_evenMomentToCriticalTrace`, `normalizedTraceMomentGerm_oddTracePreimage` (corpus `RHTower/CriticalTraceMomentGerm`) |
| `(17)`–`(19)` signed-Gamma complementary rank bound | `finrank_span_log_primesBelow`, `carrierBudget_rank_ge` (`RHTower/XiWeilCarrierBudget`) |

### The positive factorization target

| Card item | Lean name |
|---|---|
| Gram kernels are positive | `isPSDKernel_gram` (`HTGeometry/PSDKernelOperations`) |
| **`(16)` ⟹ RH**: a source Gram factorization of `B_X` proves RH | `riemannHypothesis_of_bezoutianGram` |

`riemannHypothesis_of_bezoutianGram` takes an arbitrary complex inner product space and a family
`R : {W : ℂ // 1/2 < W.re} → H` with `B_X (w, v) = ⟪R v, R w⟫`, and concludes RH.  Compatibility
under enlargement of finite node sets is automatic in this formulation.  Constructing such an `R`
remains the open gate; the theorem certifies only that it would suffice.

### The CCM chain `(20)`

The links are the Lean theorems above together with those of
`critical-logderivative-two-channel-weil-resolvent-law`:
`riemannHypothesis_of_bezoutianGram` → `riemannHypothesis_iff_posSemidef_xiCentBezoutian` →
`riemannHypothesis_iff_isPSDKernel_twoChannel` → `tendsto_apertureTwoChannelKernel` and
`riemannHypothesis_iff_forall_aperture_energy_nonneg`.  The passage from "no negative aperture
mode" to "conserved zero Morse charge" belongs to
`ccm-aperture-morse-index-conservation-law.md` and is not re-proved here.

### What is *not* formalized

- The Hedenmalm metric classification paragraph (that any continuous positive source-core form is
  nonlocal with Fourier measure on the real Xi divisor).  That is a theorem of
  `hedenmalm-theta-pair-divisor-supported-metric-law.md`; it constrains the *shape* of a solution
  to `(16)` and is not used in any statement above.
- the two open gates: the construction of `(16)`, and RH.

## Log

- 2026-08-20 — Formalized in Lean 4.  New module `RHTower/XiBezoutianPointedIncidence`; the reusable
  `isPSDKernel_gram` added to `HTGeometry/PSDKernelOperations`.  15 capstones audited to
  `propext, Classical.choice, Quot.sound`.  Promoted to stage 3.
