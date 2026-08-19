# Critical divided differences resolve the local period-incidence closure defect

- **ID:** `critical-divided-difference-period-incidence`
- **Stage:** 2-fully-proven
- **Type:** THEOREM (paper) / SOURCE-DERIVED CRITICAL RENORMING BRIDGE
- **Scientific status:** `[PROVED HERE] [BRIDGE] [LEAN TARGET] [NOT AN RH RESULT]`
- **Parents:**
  - `../../2-fully-proven/new_scientific_knowledge/multiple-gamma-period-excess-closure-phase-transition.md`
  - `critical-completed-facet-hodge-descent.md`
  - `../../1-in-progress/hypertranscendental-critical-closure-defect-principle.md`
- **Statement:** The nonclosed range of the unweighted period-incidence multiplier is removed by
  the critical trace topology forced by analytic divided differences.  On every pole-free analytic
  collar, raw translation defects lie in this critical trace space with a uniform derivative
  bound, normalized defects converge to the vertical derivative at the zero-period boundary, and
  the critical weight is unique up to bounded equivalence among diagonal weights that make the
  incidence map a topological isomorphism.

## The unweighted closure defect

Let `Lambda` be a nondiscrete additive subgroup of `C`, let `Lambda^x=Lambda\{0}`, and consider

```text
(I_Lambda x)(lambda)=lambda/(1+|lambda|) x(lambda)          (1)
```

on bounded scalar or Banach-valued families.  The parent theorem proves that `(1)` is injective
with nonclosed range in the ordinary supremum topology.  Every finite nonzero restriction is
bijective.  The defect is exactly the lack of a uniform lower bound for the source symbol at
`lambda=0`.

## Critical trace space `[PROVED HERE]`

Let `X` be a complex Banach space.  Define

```text
Y_crit(Lambda;X)
  ={y:Lambda^x->X :
      sup_lambda (1+|lambda|)/|lambda| * ||y(lambda)|| < infinity},

||y||_crit
  =sup_lambda (1+|lambda|)/|lambda| * ||y(lambda)||.        (2)
```

Then `(1)` is an isometric isomorphism

```text
I_Lambda:ell^infinity(Lambda^x;X) ~= Y_crit(Lambda;X),      (3)
```

with inverse

```text
(I_Lambda^(-1)y)(lambda)
  =(1+|lambda|)/lambda * y(lambda).                         (4)
```

Indeed, the two formulas are pointwise inverse and `(2)` gives exactly

```text
||I_Lambda x||_crit=||x||_infinity.                         (5)
```

Thus the critical range is closed and all of it is effective.  The theorem is not the assertion
that an arbitrary closure-only target in the ordinary supremum completion has acquired a
preimage.  Such a target is excluded precisely when it has infinite critical norm.

## Analytic source origin `[PROVED HERE]`

Let `U subset C` be open, let `K subset U` be compact, and choose `delta>0` such that the closed
`delta`-collar `K_delta` lies in `U`.  If `f` is holomorphic on `U` and
`0<|lambda|<delta`, then on every segment remaining in the collar,

```text
(f(z+lambda)-f(z))/lambda
  =integral_(t=0)^1 f'(z+t lambda) dt.                     (6)
```

Consequently, for any `0<epsilon<delta`,

```text
sup_(0<|lambda|<=epsilon)
  (1+|lambda|)/|lambda| * ||T_lambda f-f||_K
  <=(1+epsilon) ||f'||_(K_epsilon).                         (7)
```

The right side is finite.  Hence the raw source-defect family of every analytic germ lies in the
critical trace space on each smaller collar.  Its inverse image under `(3)` is

```text
x_f(lambda)=(1+|lambda|)(T_lambda f-f)/lambda.             (8)
```

As `lambda->0`, `(8)` converges uniformly on smaller compacta to `f'`.  Therefore the zero-period
boundary of the critically completed source action is the vertical derivative.  It is not an
extra evolution law.

The same argument iterates.  If `lambda_1,...,lambda_r` are nonzero and the full translation cube
stays in the collar, then

```text
(Delta_(lambda_1)...Delta_(lambda_r)f)(z)
  /(lambda_1...lambda_r)
 =integral_[0,1]^r
    f^(r)(z+t_1 lambda_1+...+t_r lambda_r) dt.             (9)
```

Thus normalized mixed source differences are controlled by the matching vertical derivative and
converge to it when all periods tend to zero.  Cauchy estimates give the critical factorial law

```text
||f^(r)||_K <= r! rho^(-r) ||f||_(K_rho)                  (10)
```

on nested collars.  Equations `(9)`--`(10)` are the direct source explanation of Gevrey order one
in the source-by-observable completion.

## Uniqueness of the diagonal critical topology `[PROVED HERE]`

Let `a(lambda)>0` be another diagonal weight and give the target the norm

```text
||y||_a=sup_lambda a(lambda)||y(lambda)||.                 (11)
```

The multiplier `(1)` is bounded from `ell^infinity` to `(11)` exactly when

```text
sup_lambda a(lambda)|lambda|/(1+|lambda|)<infinity.        (12)
```

Its pointwise inverse is bounded exactly when

```text
inf_lambda a(lambda)|lambda|/(1+|lambda|)>0.               (13)
```

Hence `(1)` is a topological isomorphism for `(11)` if and only if

```text
a(lambda) is boundedly equivalent to (1+|lambda|)/|lambda|. (14)
```

The critical trace topology is therefore unique up to norm equivalence inside the entire class of
diagonal source weights that make incidence boundedly effective.  Combined with `(6)`--`(10)`,
this prevents choosing a graph norm merely after seeing a desired target.

## Hermitian, spectral, and integral comparison

The critical identification separates magnitude from phase:

```text
lambda/(1+|lambda|)
  = |lambda|/(1+|lambda|) * lambda/|lambda|.               (15)
```

The first factor is absorbed by the critical norm; the second is unitary.  On the Hilbert
`ell^2` version, the critically normalized period-incidence operator is therefore a diagonal
unitary phase.  This supplies the local Hermitian and spectral closed-range realization.

The rescaling is not integral.  The original source operator `T_lambda-1` belongs to the integral
group ring, while `(T_lambda-1)/lambda` belongs only after analytic scalar extension.  Thus the
integral and critical analytic realizations are genuinely different and must be coupled by the
physical period embedding `Lambda->C`; neither should replace the other.

## Multiple-gamma consequence and boundary

For the generic multiple-elliptic-gamma hierarchy, the unweighted period-incidence map is in the
closure-only phase from order one onward.  On every source-defined pole-free collar, however, its
actual meromorphic translation-defect family satisfies `(7)` and its mixed source faces satisfy
`(9)`.

The structural rescaling

```text
x_j=T_(tau_j)-1  |->  y_j=x_j/tau_j                       (16)
```

is a diagonal automorphism after complex scalar extension.  It preserves the squarefree
Stanley--Reisner constraint ideal and compares the physical period edge with the closed Hodge
facet edge.  The unscaled `x_j` retain the integral lattice; the normalized `y_j` carry the
critical analytic realization.

`[OPEN CORE]` The full source-effectivity theorem must assemble `(16)` over all analytic collars,
the actual multiple-gamma boundary hierarchy, reflection polarization, the integral divisor
lattice, and the group--Cech monodromy realization.  This card proves the local critical topology
and its uniqueness.  It does not prove that the global enriched incidence fibre is effective or
that the five realization functors are jointly conservative.

## Parent-theory and anti-theatre verdict

Banach-valued divided differences, the fundamental theorem of calculus, Cauchy estimates, and
weighted multiplier spaces are parent mathematics.  The theorem is `[BRIDGE]`, not new scientific
knowledge.

Its positive value is exact: it identifies a source-derived topology which resolves the natural
small-period nonclosed range, proves that actual analytic source defects live in it, and proves
uniqueness among diagonal incidence-renorming topologies.  It would be theatre to call the weighted
space itself the HT classification object; the nontrivial target is the global comparison and
joint-conservativity theorem.

## Lean route

1. Formalize the weighted bounded-family equivalence `(2)`--`(5)` for a general nonzero scalar
   symbol.
2. Specialize it to `lambda/(1+|lambda|)`.
3. Formalize the Banach-valued first divided-difference identity `(6)` and the compact-collar bound
   `(7)`.
4. Extend to the mixed cube identity `(9)` only after the first-order module is cached.
5. Keep the actual multiple-gamma specialization in a separate file so no analytic source theorem
   is hidden in an abstract interface.

## Gates

- [x] critical trace space and exact isometric inverse proved
- [x] analytic collar inclusion proved
- [x] divided differences shown to converge to the vertical derivative
- [x] mixed divided-difference formula and Gevrey-one bound proved
- [x] uniqueness among diagonal critical weights proved
- [x] Hermitian phase and integral comparison separated
- [x] multiple-gamma local consequence and global proof boundary stated
- [ ] weighted bounded-family equivalence formalized in Lean
- [ ] first analytic divided-difference collar theorem formalized in Lean
- [ ] mixed analytic divided-difference theorem formalized in Lean
- [ ] actual multiple-gamma critical comparison formalized in Lean
