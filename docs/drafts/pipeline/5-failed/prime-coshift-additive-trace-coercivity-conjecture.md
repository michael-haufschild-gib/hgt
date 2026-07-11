# Prime co-shift versus additive trace coercivity

- **ID:** `prime-coshift-additive-trace-coercivity-conjecture`
- **Stage:** 5-failed
- **Type:** RETIRED CONJECTURE; post-superselection coercivity route
- **Scientific status:** `[REFUTED AT THE NATURAL TRACE GATE]`; no RH claim proved
- **Source:** the closed all-prime co-shift row, regularized polylogarithm boundary evaluation, and
  the additive heat aperture
- **Statement:** `[REFUTED IN THIS FORM]` The proposed canonical all-prime constraint row and a source-defined closed
  additive trace satisfy a quantitative lower bound away from `Re(s)=1/2`.  Evaluated on the unique
  common prime eigenline, this bound excludes every off-line zeta zero and proves RH.

## The concrete multiplicative constraint

On `H=l2(N_(>=1))`, let

```text
V_p e_n=e_(pn),
T_(p,s)=V_p^*-p^(-s)I.
```

For `Re(s)>1/2`, define the unweighted all-prime row

```text
R_s : Dom(R_s) subset H -> l2(Primes;H),
(R_s x)_p=T_(p,s)x,

Dom(R_s)
  ={x : sum_p ||T_(p,s)x||^2<infinity}.                 (1)
```

The paper theorem
`prime-coshift-eigenline-regularized-boundary-complex.md` proves:

```text
R_s is densely defined and closed,
ker R_s=C Psi_s,
Psi_s(n)=n^(-s).                                       (2)
```

No prime ordering, cutoff, summable auxiliary weights, Euler product, or zero divisor occurs in
(1).  The simultaneous prime constraint fixes the arithmetic state rather than evolving it.

## The additive trace problem `[REFUTED ON THE NATURAL ROW GRAPH]`

For `x in ker R_s`, the boundary wave is

```text
F_x(theta)=sum_(n>=1)x_n exp(i n theta).
```

The intrinsic regularized trace is

```text
B_s x
  = lim_(theta->0)
      [F_x(theta)-x_1 Gamma(1-s)(-i theta)^(s-1)],      (3)
```

and the polylogarithm expansion proves

```text
B_s Psi_s=zeta(s).                                     (4)
```

The heat-aperture energy is a positive quadratic regularization of the same additive boundary, but
the theorem `additive-heat-diagonal-generates-full-operator-algebra.md` shows that the aperture
cannot simply be adjoined to the particle diagonal while retaining superselection.  This route
therefore uses no screen algebra.  It asks for a closed trace on the graph domain of (1).

The proposed open core was to construct a dense canonical subdomain

```text
D_s subset Dom(R_s)
```

and a closed linear boundary operator

```text
B_s : D_s -> C                                           (5)
```

whose definition is an Abel/heat finite part of the actual Fourier series, whose restriction to
`ker R_s` is (3), and whose graph is independent of all admissible aperture regularizations.

This is impossible on the natural row graph.  The theorem
`../2-fully-proven/not_new_scientific_knowledge/prime-coshift-row-boundary-trace-nonclosable.md`
proves

```text
Dom(R_s)={x:sum_n omega(n)|x_n|^2<infinity}
```

with equivalent graph norm.  For the vector equal to `1/M` on `M` distinct primes and zero
elsewhere, the row graph norm tends to zero while every ordinary Abel/heat boundary value equals
one.  Thus finite-support additive evaluation is not closable in the row graph norm.  A closed
source trace extending it cannot exist.

## The RH-strength coercivity theorem

Put

```text
A_s x=(R_s x,B_s x)
  in l2(Primes;H) direct_sum C.                         (6)
```

The exact target is:

```text
[CONJECTURE: OFF-LINE COERCIVITY]

For every compact K subset {s:1/2<Re(s)<1},
there is c_K>0 such that

||R_s x||^2+|B_s x|^2
  >= c_K |Re(s)-1/2|^2 ||x||^2                         (7)

for every s in K and x in D_s.
```

Evaluating (7) at `x=Psi_s` and using (2)--(4) gives

```text
|zeta(s)|^2
  >= c_K |Re(s)-1/2|^2 zeta(2 Re(s))>0.                (8)
```

Thus (7) proves zero-freeness in the right half of the critical strip; functional equation and
Schwarz reflection then prove RH.

This statement is intentionally RH-strength.  Unlike the retired echo-to-sector implication, it is
a concrete operator estimate with a specified source row, domain obligation, norm, and constant.
It can be attacked by form methods, closed-range theory, and exact additive--multiplicative
commutators.

## Structural decomposition of the problem

Let `P_s` be the orthogonal projection onto `C Psi_s`.  A possible proof of (7) separates into two
independent estimates:

```text
||R_s(1-P_s)x||^2 >= lambda_K ||(1-P_s)x||^2,           (9)

|B_s(P_s x)| plus ||R_s(1-P_s)x||
  >= eta_K |Re(s)-1/2| ||P_s x||.                      (10)
```

Equation (9) is now proved in
`../2-fully-proven/not_new_scientific_knowledge/prime-coshift-row-orthogonal-spectral-gap.md`, with
the explicit compact-uniform bound

```text
lambda_K=(1-2^(-inf_(s in K) Re(s)))^2.
```

The proof uses the one-prime backward-shift gap on each `p`-adic ray and the commuting product of
the one-prime ground projections.  Equation (10) is therefore the true remaining
additive--multiplicative uncertainty estimate.  On the exact eigenline it is precisely the
nonvanishing burden in (8), so a proof must use how the additive trace sits on the full graph
domain, not merely restate (4).

The former spectral-gap falsifier was discharged positively.  The trace-side falsifier is now also
settled: the heat/Abel finite-part boundary value has no closable realization on the natural
row-graph core.  Therefore (7) cannot follow by the proposed two-block argument.

## Fake rejection

The proof must fail, for a visible source-side reason, under each fake:

1. **Helson twist.** Replacing the eigenvalues by `chi(p)p^(-s)` retains a common multiplicative
   eigenline and the Hilbert wall while allowing prescribed continued divisors.  The trace estimate
   must use the untwisted additive basis, not only the row norm.
2. **Shifted self-dual product.** A direct sum of the two rows at `s+a` and `s-a` models the radial
   shifts in `xi(s+a)xi(s-a)`.  The claimed purity/coercivity must reject this doubled source before
   inspecting zeros.
3. **Finite prime set.** A finite row has an enormous joint kernel.  No estimate with the required
   one-dimensional ground space can occur before the all-prime closure.
4. **Arbitrary trace extension.** A boundary functional chosen after solving the common eigenline can
   make (7) true or false at will.  The heat/Abel graph closure and its uniqueness are part of the
   theorem.
5. **Positive-observable shortcut.** Positivity of each finite-aperture heat energy does not imply
   (7); extracting the regularized trace can destroy positivity.

## Why ordinary index and derived limits are absent

The reduced boundary map `C Psi_s -> C` has index zero both on and off the divisor because kernel and
cokernel appear together.  An ordinary Fredholm index is therefore blind.

Nor is (6) defined as a derived inverse limit of finite acyclic fibers.  The no-go
`acyclic-finite-fibers-derived-limit-zero.md` proves that such a limit cannot create cohomology.  The
closed row (1) is the all-prime object from the outset; any defect is a closed-range or trace-domain
phenomenon of this specified operator.

## Terminal verdict

The graph completion and closability test are complete.  The natural scalar trace fails before a
Green identity can be posed.  The route is retired in its stated form.

A successor must strengthen the graph by a separately source-defined additive operator, retain a
vector-valued boundary object, or introduce a genuinely second analytic direction.  Merely choosing
a smaller trace domain or defining `B_s x=x_1 zeta(s)` would abandon the canonical source premise.

## Lean surface

The row's algebraic coordinate identities, the spectral gap, and the nonclosability sequence are
elementary enough for a future concrete formalization.  No abstract wrapper is justified: the
formal endpoint should include the actual multiplicative shifts, graph-domain identity, and
prime-supported countersequence.

## Gates

- [x] unique common eigenline and Hilbert threshold proved
- [x] canonical all-prime row proved densely defined and closed
- [x] regularized trace identified on the eigenline
- [x] RH implication of the coercive estimate proved
- [x] derived-limit, ordinary-index, and joint-algebra shortcuts excluded
- [x] spectral gap for `R_s` on the orthogonal complement
- [x] natural graph-domain additive trace refuted by an explicit nonclosability sequence
- [x] exact scalar-trace route retired
- [ ] formulate a successor only with a genuinely stronger source object
