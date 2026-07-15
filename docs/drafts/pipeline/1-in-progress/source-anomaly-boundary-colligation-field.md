# The source-anomaly boundary-colligation field

- **ID:** `source-anomaly-boundary-colligation-field`
- **Stage:** 1-in-progress
- **Type:** FOUNDATIONAL HT CONJECTURE / SOURCE-SPECIFIC UNIFIED FIELD
- **Scientific status:** `[CONJECTURE] [FINITE ALGEBRAIC SKELETON LEAN-FORMALIZED] [CURVATURE-ONLY AND KINEMATIC-FIELD NO-GOS PROVED] [NOVELTY OPEN]`
- **Parents:**
  - `clock-descent-anomaly.md`
  - `ind-flat-pro-curved-boundary-transfer.md`
  - `constraint-curvature-integration-stack.md`
- **Statement:** A constrained hypertranscendental source is not represented by a clock curvature
  alone. Its primary finite data are an upper-triangular boundary colligation together with the
  source-specific descent anomaly. Hypertranscendence is maximal finite anomaly range; thin source
  constraint is bounded transverse variation of that anomaly across observable resolution.

## 1. Exact finite object

Let

```text
O_N --i_N--> O_(N+1) --p_N--> O_N,       p_N i_N=1,       (1)
```

and let `T_N(a)` be proposed finite shadows of a source operation `S(a)`. Write

```text
b_N=1-i_N p_N,                                             (2)
alpha_N(a)=T_N(a) q_N-q_N S(a),                            (3)
kappa_N(a)=p_N T_(N+1)(a)-T_N(a)p_N.                       (4)
```

If forward assembly is exact,

```text
T_(N+1)(a)i_N=i_N T_N(a),                                  (5)
```

then the Lean-formalized boundary-colligation reconstruction is

```text
T_(N+1)(a)
 = i_N T_N(a)p_N + i_N kappa_N(a) + delta_N(a),             (6)
delta_N(a)=b_N T_(N+1)(a)b_N.                              (7)
```

Equivalently, relative to `O_(N+1)=i_N O_N + ker(p_N)`,

```text
T_(N+1)(a) = [ T_N(a)   beta_N(a)
               0        delta_N(a) ],                     (8)
beta_N(a)=p_N T_(N+1)(a)|ker(p_N).                         (9)
```

The complete finite comparison datum is therefore

```text
C_N(a)=(T_N(a), beta_N(a), delta_N(a), alpha_N(a)).        (10)
```

It is a colligation over observable resolution, not an evolution in time.

## 2. Curvature-only reconstruction no-go and positive theorem

For every endomorphism `g` of `O_(N+1)`, the boundary perturbation

```text
T'_(N+1)=T_(N+1)+b_N g b_N                                (11)
```

preserves both forward compatibility and curvature:

```text
T'_(N+1)i_N=T_(N+1)i_N,                                   (12)
kappa_N(T')=kappa_N(T).                                    (13)
```

Thus curvature, even with the lower action and split clock, forgets the whole boundary
self-symbol. This no-go is Lean-formalized.

**Positive reconstruction theorem.** Equality of lower action, curvature, and boundary
compression forces equality of the higher action. This is the exact uniqueness theorem obtained
from `(6)` and is Lean-formalized.

Consequently the earlier curvature field and transfer field are strict quotients of the true
finite object `(10)`.

## 3. Kinematic-field no-go

The Taylor translation matrices and their factorial boundary transfers are universal jet
kinematics. They are defined without Gamma or any other source. Therefore

```text
(beta_N,delta_N) of formal translation alone               (14)
```

cannot distinguish Gamma from an arbitrary analytic germ and cannot be the HT source field.

**Positive replacement.** The universal colligation is the background observation calculus. The
source enters through `S`, its admissible tangent/corona, the affine normalization, and the
descent anomaly `(3)`. Gamma supplies one source-specific section of the universal translation
colligation: its tangent is period one and its affine shift cocycle fixes the section.

For Gamma, the Lean-formalized boundary symbol is canonical:

```text
delta_N=b_N E_(N+1)b_N=b_N,                                (15)
```

so it is the identity on the new highest-jet line, while `beta_N` is the factorial tail.

## 4. Exact algebraic laws

The anomaly and curvature obey parallel derivation laws under the constraint algebra:

```text
alpha(S T,A B)=A alpha(T,B)+alpha(S,A)T,                   (16)
kappa(A B)=kappa(A)B+A kappa(B).                           (17)
```

Equation `(16)` is Lean-formalized as `clockDescentAnomaly_comp_constraint`; `(17)` is formalized
as `clockShadowCurvature_comp_shadow`. Hence the augmented comparison operator

```text
A_N(a) = [ T_N(a)      alpha_N(a)
           0           S(a)       ]                        (18)
```

is multiplicative whenever the source and shadow assignments are multiplicative.

Across resolution, the Lean-formalized Bianchi identity is

```text
p_N alpha_(N+1)(a)-alpha_N(a)
  = kappa_N(a) q_(N+1).                                   (19)
```

Under `(5)`, the right side factors through the new boundary layer by `(9)`.

## 5. Capacity--thinness conjecture

**[CONJECTURE — MAXIMAL SECTION / THIN VARIATION]** A regular source-minimal constrained HT germ
admits a source-canonical completion of `(10)` satisfying:

```text
range(alpha_N(a)|ker S(a))=range(T_N(a))                  (20)
```

for every finite clock, while

```text
sup_N dim B_N < infinity                                  (21)
```

for a finite-rank source constraint. Thus its finite comparison anomaly has maximal observable
range, but its covariant variation `(19)` is uniformly transverse and thin.

This is the precise proposed meaning of

> Hypertranscendence is infinite algebraic clock capacity concentrated on a thin constraint
> boundary.

The word `capacity` refers to the independent finite observables in `(20)`, not time. The boundary
is the resolution-transverse carrier in `(19)` and `(21)`.

**Falsifier.** A source-minimal constrained HT germ for which every faithful clock either loses
finite-observable freedom or has necessarily unbounded transverse boundary width.

## 6. Source-horizontalization conjecture

**[CONJECTURE — HT AS NO FINITE HORIZONTAL SECTION]** In the source-canonical analytic category,
a germ is differentially algebraic exactly when its completed anomaly-colligation admits a
finite-dimensional algebraic horizontalization compatible with the full source algebra. A germ is
hypertranscendental exactly when no such finite horizontalization exists, even though every finite
clock is observable and the transverse boundary width may remain bounded.

This is not the false claim that a scalar transfer series has infinite Hankel rank. Gamma's
factorial translation transfer is universal and cannot certify Gamma hypertranscendence. The
criterion concerns simultaneous horizontalization of `(S,T,alpha,beta,delta)` and all source
syzygies.

**Falsifier.** A known differentially algebraic source with no finite source-algebra
horizontalization, or a known hypertranscendental source with one.

## 7. Unified integration object

Let `Coll_R(x)` be the derived moduli of global analytic realizations of the completed
anomaly-colligation field in a realization category `R`. It retains domain, topology, affine
origin, source algebra, boundary symbol, transfer, and reflection.

**[CONJECTURE — COLLIGATION INTEGRATION STACK]** The common object behind the obstruction chains is

```text
J_x(R)=hofib_(C_x)(GlobalColl_R(x)->LocalColl_R(x)).        (22)
```

Its faces are literal invariants:

1. continuation failure is emptiness after enlarging the source domain;
2. noncanonical boundary conditions are multiple connected components;
3. monodromy is holonomy of the local colligation torsor;
4. spectral incompleteness is tangent homology or failure of minimal realization;
5. positivity failure is absence of a positive reflected orientation.

Curvature-only fibers identify realizations that differ by `(11)` and are therefore too coarse.

## 8. Self-dual degeneracy conjecture

Reflection should not act only on `beta_N beta_N^*`. It acts on the complete augmented
colligation `(18)`, pairing outgoing transfer, boundary self-symbol, and source anomaly.

**[CONJECTURE — SELF-DUAL COLLIGATION DEGENERACY]** For a reflected family `x_s`, the common
degeneracy spectrum is the support where the minimal self-dual realization of `C_(x_s)` ceases to
be a single oriented object. Fixed-locus degeneracy is forced only after proving that reflection
turns the full colligation into a conservative or positive-real realization; reflection symmetry
alone still permits off-fixed paired degeneracies.

## 9. RH pressure test only

**[CONJECTURE; NOT AN RH RESULT]** Different RH proof chains may be realizations of one
source-anomaly colligation only if they preserve `alpha`, `beta`, `delta`, affine origin, topology,
and reflection. Spectral incompleteness, continuation failure, positivity failure, monodromy, and
noncanonical boundary conditions would then be different invariants of `(22)`. Critical zeros
would be the common self-dual degeneracy spectrum of that object.

No zeta function, completed xi function, divisor, or zero-indexed operator may define the field.
The source colligation must be constructed independently from prime and archimedean constraints.
No such construction or cross-chain comparison is presently proved.

## 10. Parent-theory collision and novelty gate

- Upper-triangular operator matrices, system colligations, characteristic functions, mapping
  cones, affine cocycles, and conservative realizations are established parent theory.
- The reconstruction theorem `(6)` is elementary split linear algebra.
- The anomaly and curvature Leibniz laws are derivation identities.
- The candidate-new residue is the source-canonical HT completion satisfying simultaneous maximal
  range `(20)`, bounded transverse variation `(21)`, the finite-horizontalization criterion, and
  realization equivalence `(22)` across genuinely different analytic categories.

The proposal fails the novelty gate if it reduces to an ordinary conservative system realization
after forgetting the source algebra and finite-observable freedom.

## Gates

- [x] curvature-only reconstruction no-go Lean-formalized
- [x] full boundary-colligation reconstruction and uniqueness Lean-formalized
- [x] anomaly constraint-algebra cocycle Lean-formalized
- [x] anomaly/curvature Bianchi law Lean-formalized
- [x] Gamma unit boundary self-symbol Lean-formalized
- [x] universal-translation/source-specific-field distinction stated
- [ ] boundary-block multiplication law Lean-formalized
- [ ] one source-canonical completed anomaly-colligation constructed
- [ ] finite-horizontalization criterion proved in one nontrivial category
- [ ] one non-Gamma source field constructed
- [ ] two obstruction realizations proved equivalent as source colligation integrations
- [ ] independent novelty and significance audit
