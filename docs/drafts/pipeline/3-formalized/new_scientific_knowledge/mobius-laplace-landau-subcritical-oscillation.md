# Möbius--Laplace Landau subcritical two-sided oscillation

- **ID:** `mobius-laplace-landau-subcritical-oscillation`
- **Stage:** 3-formalized
- **Type:** THEOREM (paper + Lean 4)
- **Source:** `mobius-laplace-critical-renewal-law.md` and
  `formal/GaloisForLFunctions/RHTower/MobiusLaplaceCriterionFrontier.lean`
- **Statement:** Every subcritical half-power normalization of the discrete Möbius--Laplace
  transform is unbounded in both signs at the zero edge.
- **Scientific status:** `[PROVED HERE] [CONCRETE THEOREM NOT FOUND IN CHECKED LITERATURE]`
  `[CLASSICAL LANDAU CONSEQUENCE] [PRIOR NUMERICAL/HEURISTIC ANTICIPATION]`
  `[NOT A PRIORITY CLAIM] [NOT RH] [NO COMPUTATION]`

## Goal

For

```text
Phi(x)=sum_(n>=1) mu(n) exp(-n x),      x>0,
```

prove, unconditionally, that for every `0<epsilon<1/2`, every `A>0`, and every `delta>0`,
there are `x_+,x_- in (0,delta)` with

```text
Phi(x_+) >  A x_+^(-1/2+epsilon),
Phi(x_-) < -A x_-^(-1/2+epsilon).                         (L1)
```

Equivalently,

```text
limsup_(x->0+) x^(1/2-epsilon) Phi(x)=+infinity,
liminf_(x->0+) x^(1/2-epsilon) Phi(x)=-infinity.          (L2)
```

Consequently `Phi` has infinitely many positive-real zeros accumulating at `0`.  This advances
the compact negative interval already formalized in the parent module to cofinal zero-edge
oscillation.  It is a lower oscillation theorem, not the missing upper estimate
`Phi(x)=O(x^(-1/2))`; therefore it does not imply RH.

## Gates

- [x] 0 -> 1: concrete source, exact Mellin transform, and non-circular attack fixed
- [x] 1 -> 2: dependency-closed paper proof; no RH, simplicity, or zero-sum hypothesis
- [x] 2 -> 3: formalize continuous Landau transfer, both sign collisions, excursions, and zeros
- [ ] 3 -> 4: specialist priority audit and standalone publication certificate

## Exact Mellin carrier

The parent module proves, for `Re s>1`,

```text
integral_(0,infinity) Phi(x)x^(s-1) dx = Gamma(s)/zeta(s). (L3)
```

It also proves exponential decay for `x>=1`.  Hence

```text
E(s)=integral_(1,infinity) Phi(x)x^(s-1) dx               (L4)
```

is entire: on every compact set of `s`, exponential decay dominates every occurring real power
of `x`, uniformly with all complex derivatives.

Fix `epsilon in (0,1/2)` and put

```text
a=1/2-epsilon.                                            (L5)
```

For `K in R`, define on `(0,1]`

```text
h_K(x)=Phi(x)+K x^(-a).                                   (L6)
```

Its Mellin transform initially satisfies

```text
H_K(s)=integral_(0,1) h_K(x)x^(s-1) dx
      =Gamma(s)/zeta(s)-E(s)+K/(s-a),       Re s>1.       (L7)
```

No rearrangement at the zero edge occurs in `(L7)`: `(L3)` is used only in its proved absolute
half-plane, `(L4)` is subtracted there, and the elementary power integral supplies the last term.

## Landau boundary lemma

Use the following classical theorem in zero-edge Mellin form.

> **Landau boundary lemma.** Let `h:(0,1]->R` be locally integrable and of at most power growth at
> `0`.  Let `sigma_c` be the abscissa of convergence of
> `integral_(0,1)h(x)x^(s-1)dx`.  If `h` has one constant sign on some `(0,delta)`, then the real
> point `s=sigma_c` is a singularity of the function represented by the integral.

For completeness, substitute `x=exp(-u)`.  The Mellin integral becomes the ordinary Laplace
transform

```text
integral_(0,infinity) h(exp(-u)) exp(-s u) du.            (L8)
```

Changing `h` on a bounded `u`-interval adds an entire function, so assume the integrand has one
sign everywhere.  If its transform were analytic across its real convergence abscissa
`sigma_c`, choose `s_0>sigma_c` so close to `sigma_c` that the Taylor disc around `s_0` crosses
the boundary while remaining inside the union of the convergence half-plane and that analytic
neighborhood.  Differentiation under the integral gives

```text
(-1)^m H^(m)(s_0)
  =integral_(0,infinity) u^m h(exp(-u))exp(-s_0 u) du.    (L9)
```

After replacing `h` by `-h` if needed, every right side is nonnegative.  Evaluate the Taylor
series at `s_0-r<sigma_c`; Tonelli and the exponential series give

```text
sum_(m>=0) r^m/m! integral u^m h(exp(-u))exp(-s_0u)du
 =integral h(exp(-u))exp(-(s_0-r)u)du < infinity,         (L10)
```

contradicting definition of `sigma_c`.  This proves the lemma and also shows why eventual, rather
than global, one-sided sign is sufficient.

## Location and regularity of the convergence wall

The trivial bound `|Phi(x)|<=1/x` for `0<x<=1` and `a<1` imply that `H_K` converges absolutely
for every real `s>1`.  Thus its finite convergence abscissa satisfies

```text
sigma_c<=1.                                               (L11)
```

The already-proved infinite Xi-divisor theorem supplies an Xi zero `rho_0`.  Reflect it by
`rho -> 1-rho` if necessary.  The functional equation preserves zerohood, so this gives a zero
`rho` with

```text
Re rho>=1/2,   Im rho!=0,   zeta(rho)=0.                  (L12)
```

Every Xi zero lies in the open critical strip, and the real strip is zero-free, so `rho` is
nonreal.  No simplicity assumption is needed.  Gamma is zero-free, so `Gamma(s)/zeta(s)` has a
genuine pole at `rho`; the entire term `E` and rational term `K/(s-a)` are analytic there because
`a<1/2` is real.  If `sigma_c<Re rho`, the defining integral would be holomorphic at `rho`;
identity continuation from `Re s>1` through `(L7)` would remove this genuine pole.  Therefore

```text
1/2<=Re rho<=sigma_c<=1.                                  (L13)
```

The right side of `(L7)` is analytic at every real point of `[1/2,1]`:

- zeta has no real zero in `(0,1)`;
- `1/zeta` has a removable zero at the pole `s=1`;
- Gamma has neither zero nor pole there;
- `a<1/2`, so `K/(s-a)` has no pole there;
- `E` is entire.

In particular it is analytic at the real point `sigma_c`.  The Landau boundary lemma now forbids
`h_K` from having either eventual sign.  Hence, for every `delta>0`, `h_K` takes both positive and
negative values in `(0,delta)`.

## Two-sided subcritical amplification

Let `A>0`.

- Set `K=-A`.  A positive value of `h_(-A)` gives
  `Phi(x)>A x^(-a)` arbitrarily near `0`.
- Set `K=A`.  A negative value of `h_A` gives
  `Phi(x)<-A x^(-a)` arbitrarily near `0`.

This proves `(L1)` and `(L2)`.  Since the parent module proves that `Phi` is real and continuous
on `(0,infinity)`, every sufficiently small interval contains values of both signs and therefore
contains a zero between two such values.  Taking `delta=1/m` and recursively shrinking below the
previous zero constructs infinitely many distinct zeros converging to `0`.

## Hostile audit

1. **Hidden RH input.** None.  Infinite Xi-zero supply is unconditional.  Functional-equation
   reflection chooses a zero in the closed right half of the strip; it does not put every zero,
   or even this selected zero, on the critical line.
2. **Simple-zero or zero-sum hypothesis.** None.  Any positive multiplicity still makes
   `Gamma/zeta` singular.  No explicit-formula sum over zeros is used.
3. **Boundary-pole collision.** Comparison exponent is `a=1/2-epsilon`, strictly left of the
   forced wall.  At the sharp exponent `a=1/2`, `K/(s-a)` creates a real boundary pole and the
   Landau contradiction fails.  The proof deliberately does not claim sharp
   `Omega_+/- (x^(-1/2))`.
4. **Convergence versus analytic continuation.** Pole at `rho` only lower-bounds the actual
   integral abscissa.  Landau is applied at that actual abscissa, not at a guessed `1/2` wall.
5. **Real-axis regularity.** Absence of real zeta zeros in `(0,1)` and removability at `1` are
   essential.  A nonreal pole alone would not contradict an eventual sign if a real singularity
   occurred at same convergence boundary.
6. **Sign change versus amplitude.** Applying Landau separately to every shifted comparison
   `Phi+Kx^(-a)`, not only to `Phi`, yields arbitrary amplitude `A` in both signs.
7. **No upper bound.** `(L2)` is compatible with the conjectural sharp upper size
   `O(x^(-1/2))`.  It supplies no Mellin continuation to `Re s>1/2` and no RH proof.
8. **No computation.** Proof uses only Mellin identity, exponential tail, unconditional Xi-zero
   supply, functional-equation reflection, real-strip zero-freeness, and Landau's theorem.

## Literature audit

Liflandsky's July 2026 paper proves the Mellin identity and RH criterion and contains a source
comment expecting the sharper statement

```text
Phi(x)=Omega_+/- (x^(-1/2)),
```

but explicitly does not pursue it.  Its text contains no Landau argument, subcritical
`Omega_+/-`, cofinal sign theorem, or accumulating-real-zero theorem.

C. E. Froberg's 1966 *Numerical studies of the Mobius power series* studies the same ordinary
power series under `q=exp(-x)` and reports numerical/heuristic oscillation near `q=1`; it is prior
anticipation, not a checked rigorous proof of `(L1)`.  The general mechanism is classical
Landau oscillation and is already used elsewhere in this corpus for Xi-divisor exponential sums.
Accordingly the only candidate scientific delta is the rigorous concrete Möbius--Laplace theorem
`(L1)`--`(L2)` and its zero-edge consequence; no claim is made that Landau's mechanism is new.

Primary sources checked:

- S. Liflandsky, *Explicit formula for the discrete Laplace transform of the Mobius function,
  related special functions, and a criterion for the Riemann hypothesis*, arXiv:2607.09797v2.
- C. E. Froberg, *Numerical studies of the Mobius power series*, BIT 6 (1966), 191--211,
  DOI 10.1007/BF01934354.
- J. Lay, *Sign changes in Mertens' first and second theorems*, citing Ingham's Theorem H for the
  Landau boundary lemma and illustrating the same comparison-shift method.

## Lean formalization

`LandauIntegralTransfer.lean` proves the reusable continuous Taylor--Tonelli theorem for a
nonnegative random variable: analytic continuation of its complex MGF through a closed ball
forces every positive exponential moment strictly inside that ball.

`MobiusLaplaceLandauOscillation.lean` then formalizes the complete source specialization:

- unconditional sharp geometric estimate `||Phi(x)|| <= 1/x` and classical Mellin convergence;
- exact power-comparison Mellin identity and entire cutoff-tail transform;
- low-height quotient analyticity from `xi_ne_zero_of_abs_im_le_four`;
- positive density measure, translated MGF identity, and both Landau sign transfers;
- analytic reconstruction of `Gamma/zeta` across a half-plane with edge below `1/2`;
- collision with `xiDivisorSupport_infinite` after functional-equation reflection;
- arbitrary two-sided subcritical excursions and positive zeros below every `delta>0`.

All target modules compile with `lake env lean`; no `sorry`, `admit`, `axiom`, `opaque`, or
`unsafe` declaration is introduced.  Remaining open endpoint is still exact exponent `1/2`.

## Frontier consequence

The half-power exponent is a genuine zero-edge oscillation barrier from below: every weaker power
normalization fails by unbounded positive and negative excursions.  Any viable proof of the open
upper bound must therefore control an intrinsically cofinal oscillatory source; eventual
positivity, monotonicity, finite sign charts, and subcritical absolute majorants are impossible.
The remaining open core is exactly sharp upper cancellation at exponent `1/2`, or equivalently
the already formalized Mellin continuation wall.

## Log

- 2026-07-22 -- Lcm-kernel route retired as standard join-matrix incidence factorization.
- 2026-07-22 -- Derived Landau comparison theorem `(L1)` from exact Mellin carrier and a
  right-half Xi zero.
- 2026-07-22 -- Hostile audit isolated strict `epsilon>0` as essential; sharp comparison collides
  with a real Mellin pole.
- 2026-07-22 -- Checked Liflandsky, Froberg, Hardy, and Landau parents; classified theorem as
  concrete classical consequence with prior heuristic anticipation, not a priority claim.
- 2026-07-22 -- Removed unnecessary Hardy dependency: reflected unconditional Xi-zero supply
  already forces the Mellin convergence wall to `Re >= 1/2`.
- 2026-07-22 -- Formalized continuous Landau Taylor--Tonelli transfer, source cutoff/tail
  reconstruction, both sign obstructions, quantified excursions, and zero accumulation in Lean 4.
