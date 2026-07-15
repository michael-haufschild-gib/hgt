# Before There Was Time: hypertranscendence beyond the characteristic horizon

- **ID:** `pretemporal-principal-symbol-hypertranscendence-horizon`
- **Stage:** 2-fully-proven / needs-audit
- **Type:** THEOREM / FILTERED DIFFERENTIAL ALGEBRA / LAW GEOMETRY
- **Scientific status:** `[PROVED HERE] [NOVELTY UNVERIFIED] [LEAN OPEN]`
- **Statement:** For a constraint-compatible derivation algebra acting triangularly on an
  algebraically free cyclic filtration, differential algebraicity is exactly the vanishing of the
  principal raising symbol.  The differentially algebraic laws form a projective characteristic
  horizon; every noncharacteristic law is hypertranscendental.

## 1. The external object

Let `k subset K subset L` be characteristic-zero fields.  Let `g` be a finite-dimensional
`k`-vector space and let

```text
rho:g -> Der_k(L)
```

be a `k`-linear family of derivations preserving `K`.  When `g` is closed under commutators, its
bracket is the law algebra imposed by the constraints.  No element of `g` is initially designated
as time.

Fix a sequence `(u_n)_(n>=0)` in `L`, with `u_0=x`, and the cyclic filtration

```text
F_n=span_K{u_0,...,u_n}.
```

Assume `(u_n)` is algebraically independent over `K`.  Suppose there is a `k`-linear principal
symbol

```text
sigma:g -> K
```

such that for every `A in g` and every `n>=0`,

```text
rho(A)u_n = sigma(A)u_(n+1) mod F_n.                          (1)
```

The map `sigma` is not an evolution law.  It measures whether a constraint-compatible derivation
crosses the next layer of the observable's algebraically free filtration.

## 2. Principal-symbol horizon theorem `[PROVED HERE]`

For every nonzero `A in g`, the element `x` is differentially algebraic over `K` for `rho(A)` if
and only if

```text
sigma(A)=0.                                                   (2)
```

Consequently the complete differentially algebraic direction spectrum is

```text
Chron_g(x)=P(ker sigma) subset P(g).                          (3)
```

Every law direction outside this projective characteristic set is hypertranscendental.  If
`sigma` has one-dimensional image, `(3)` is a projective hyperplane.  Over `R` or `C`, this proper
closed set is exactly the topological boundary between itself and the open dense
hypertranscendental law region.

### Proof

Fix `A` and write `D=rho(A)`, `s=sigma(A)`.  Equation `(1)` means that

```text
D u_n = s u_(n+1) + sum_(j<=n) q_(n,j) u_j,   q_(n,j) in K.  (4)
```

Induction gives

```text
D^n x = s^n u_n mod F_(n-1).                                 (5)
```

Indeed, applying `D` to the leading term in order `n` produces `s^(n+1)u_(n+1)`.
The derivative `D(s^n)` and the derivatives of every lower-filtration term stay in `F_n`, so they
cannot alter the new leading coefficient.

If `s` is nonzero, then for every `N` the finite change

```text
(u_0,...,u_N) -> (x,Dx,...,D^N x)
```

is lower triangular over `K` with diagonal `(1,s,...,s^N)`.  It is invertible.  Algebraic
independence of every finite `u`-packet therefore transfers to every finite `D`-jet packet, so the
complete `D`-jet family is algebraically independent.  Thus `x` is hypertranscendental for `D`.

If `s=0`, equation `(4)` at `n=0` gives `Dx=q_(0,0)x`.  Hence `x` satisfies the first-order linear
differential equation

```text
Dx-q_(0,0)x=0.
```

This proves `(2)` and `(3)`.  `QED`

No assumption says that the mixed-direction jets are independent; their independence is the
triangular conclusion.

## 3. Affine Ward algebra as an exact model

Let `T,E` satisfy `[E,T]=wT`, let `Ex=0`, and take `u_n=T^n x`.  Then

```text
E u_n=n w u_n.
```

For `A=aT+bE`,

```text
A u_n=a u_(n+1)+bnw u_n.
```

Thus `sigma(aT+bE)=a`, and the characteristic horizon is the single projective dilation ray
`{[E]}`.  This recovers the exact affine hypertranscendence horizon without needing the closed
Stirling formula.

For the affine centralizer of period shears, scalar extension from `k` to the period field `K`
aligns the horizontal generators `partial_z` and `omega_i partial_z` into one translation line.
The resulting `K`-law algebra is two-dimensional, its symbol has rank one, and the dilation ray is
a genuine projective hyperplane in `P^1(K)`.

## 4. Anti-theatre boundary

The theorem is not a new proof of hypertranscendence from nothing.  It requires one algebraically
free source filtration `(u_n)`.  Its content is exact propagation from that source to **every**
noncharacteristic law direction and exact identification of all exceptional directions.

The pair `(g,sigma)` must be reconstructed independently from the constraints and regularity class.
Choosing a filtration or symbol after inspecting `x` can manufacture a desired horizon and is
prohibited.  A physical application must prove:

1. `g` is the complete regular constraint centralizer of the observable algebra;
2. the filtration is intrinsic, for example an operator-order, insertion, or ultraviolet
   filtration;
3. `(1)` is a Ward or locality consequence;
4. at least one source orbit `(u_n)` is unconditionally algebraically independent.

## 5. QFT and cosmological interpretation `[CONJECTURE]`

Before a time direction exists, a constrained observable theory may supply a filtered derivation
algebra.  The symbol `sigma` divides projective law space into characteristic rays, which fail to
cross the observable filtration, and noncharacteristic rays, which generate an infinite
algebraically free jet tower.  The characteristic set is a literal algebraic horizon: information
about finite laws is confined to it, while every transverse ray is hypertranscendental.

This resembles the characteristic variety of a differential operator, but its invariant is
different: it classifies the derivation directions in which a fixed observable becomes
differentially algebraic.  A many-worlds reading would treat projective rays as candidate emergent
laws and the complement of the horizon as the hypertranscendental phase.  That interpretation is
not a theorem about reality until a concrete QFT observable net realizes all four requirements in
Section 4.

## 6. External novelty gate

Novelty is judged only against external literature.  The following are standard and excluded from
novelty:

- associated graded modules and principal symbols;
- characteristic and noncharacteristic directions in PDE and D-module theory;
- lower-triangular preservation of algebraic independence;
- highest-weight and filtered Lie-algebra modules;
- parametrized differential Galois methods for one chosen derivation.

The candidate claim is their differential-algebraic synthesis: the exact identity `(3)` between a
projective ordinary-DA spectrum and a principal-symbol characteristic set, followed by a
nontrivial special-function or QFT instantiation.  No inspected source states this identity.  This
is an absence-of-hit report, not a priority claim.  The external audit must specifically compare
against Kolchin's differential-type/typical-dimension theory, differential modules for solvable Lie
algebras, characteristic varieties of cyclic D-modules, and hypertranscendence under changes of
derivation.

The abstract theorem alone is too elementary for the significance gate.  A Fields-level result
would require the intrinsic symbol of a central hypertranscendental function or observable to
compute a previously inaccessible law spectrum.

## 7. Elliptic-gamma target `[OPEN CORE]`

For additive multiple elliptic gamma, the constraint shears reconstruct the affine translation and
dilation algebra.  The source filtration is

```text
u_n=partial_z^n Gamma_e.
```

The remaining obligations are to put all variables in one meromorphic differential field, prove
simultaneous-scale invariance, and prove algebraic independence of this complete translation orbit
there.  If those obligations close, `(3)` computes the whole regular affine law spectrum rather
than merely restating one-variable hypertranscendence.

## 8. RH impact

The ordinary zeta differential field has a one-point projective law space, so the theorem gives no
RH step.  A possible downstream use would require a scale-covariant multiparameter completed
`L`-function with an intrinsic filtered law algebra and a symbol whose characteristic set interacts
with the critical-line constraint.  No such source is presently established.

## 9. Lean route

1. Formalize a filtered sequence and the one-step principal-symbol congruence `(1)`.
2. Prove the all-order triangular congruence `(5)` without an axiom of jet independence.
3. Build each finite lower-triangular matrix and prove its determinant is the nonzero product of
   the symbol powers.
4. Transfer finite algebraic independence and then the complete jet-family independence.
5. Derive the kernel-direction first-order equation and the exact equivalence `(2)`.
6. Instantiate the already formalized affine Ward-filtration lemmas.

Every proof must be unconditional in Lean before publication.

## 10. Gates

- [x] external object identified as a filtered constraint-compatible law algebra
- [x] principal-symbol law stated independently of a chosen time ray
- [x] exact characteristic-horizon theorem proved on paper
- [x] affine Ward algebra recovered as a special case
- [x] source assumption and physical anti-theatre boundary explicit
- [ ] independent external novelty audit
- [ ] unconditional Lean proof of the principal-symbol horizon theorem
- [ ] rigorous elliptic-gamma field and source orbit
- [ ] complete physical constraint-centralizer instantiation
