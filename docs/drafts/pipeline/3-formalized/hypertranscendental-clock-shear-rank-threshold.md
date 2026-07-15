# Rank two is the first hypertranscendental clock-shear phase

- **ID:** `hypertranscendental-clock-shear-rank-threshold`
- **Stage:** 3-formalized
- **Type:** GENERAL HT THEOREM / EXACT RECONSTRUCTION LAW
- **Scientific status:** `[PROVED HERE] [LEAN FORMALIZED] [CANDIDATE NEW SCIENTIFIC KNOWLEDGE]`
- **Statement:** A scalar free HT field admits no reversible differential reconstruction drift,
  whereas a free rank-two HT field admits a reversible constraint whose stable core is the whole
  field but whose original coordinate has exact reconstruction order `n` in the `n`-th source
  frame.

## Theorem

Let `C` be a characteristic-zero differential field of constants and let `x,y` be differentially
independent over `C`.  Put

```text
F=C<x,y>.
```

Define a differential substitution and its inverse by

```text
Phi(x)=y,             Psi(x)=-D x+y,
Phi(y)=x+D y,         Psi(y)=x.                           (1)
```

Let

```text
P_m=C(D^j x,D^j y : 0<=j<m),
b_n=Psi^n(x).                                               (2)
```

Then:

1. `Phi` and `Psi` are mutually inverse differential automorphisms of `F`.
2. The stable core is maximal:

   ```text
   intersection_n Phi^n(F)=F.                              (3)
   ```

3. The inverse coordinates obey the exact triangular law

   ```text
   b_n=(-1)^n D^n x+r_n,        r_n in P_n.                (4)
   ```

4. For all `n,m`,

   ```text
   b_n in P_m  iff  n<m.                                   (5)
   ```

5. Consequently the least differential order required to reconstruct `x` from the `n`-th source
   frame `(Phi^n(x),Phi^n(y))` is exactly `n`.

In contrast, every differential automorphism of the scalar free field `C<q>` fixing `C` is a
Möbius transformation of `q`.  It and all its iterates have order zero.  Hence positive reversible
reconstruction drift is impossible in rank one and possible in rank two.

## Proof

The two compositions in `(1)` are identities on generators:

```text
Phi(Psi(x))=Phi(-D x+y)=-D y+(x+D y)=x,
Phi(Psi(y))=Phi(x)=y,

Psi(Phi(x))=Psi(y)=x,
Psi(Phi(y))=Psi(x+D y)=(-D x+y)+D x=y.
```

The universal property of the free differential rational field therefore makes `Phi` and `Psi`
inverse differential automorphisms.  This proves `(3)`.

The first backward coordinates satisfy

```text
b_0=x,
b_1=-D x+y,
b_(n+2)=-D b_(n+1)+b_n.                                  (6)
```

Formula `(4)` follows by two-step induction.  It is immediate for `n=0,1`.  If

```text
b_(n+1)=(-1)^(n+1)D^(n+1)x+r_(n+1),
```

then `(6)` gives the required leading term at order `n+2`; the remaining expression is

```text
r_(n+2)=-D r_(n+1)+b_n.
```

Differentiation maps `P_(n+1)` into `P_(n+2)`, and `(4)` at level `n` gives
`b_n in P_(n+1)`.  Hence `r_(n+2) in P_(n+2)`.

Differential independence makes all labelled jets of `x,y` algebraically independent.  Therefore
`D^n x` is transcendental over `P_n`.  Since the coefficient `(-1)^n` in `(4)` is nonzero,
`b_n` cannot belong to `P_n`; but `(4)` also gives `b_n in P_(n+1)`.  Monotonicity of the prefix
fields proves `(5)`.

Finally, `x=Phi^n(b_n)`, so `(4)` supplies an order-`n` reconstruction in the `n`-th frame.  Any
order-`m<n` reconstruction, pulled back by `Psi^n`, would put `b_n` in `P_(m+1)` with `m+1<=n`,
contradicting `(5)`.  Thus the cost is exact.

The scalar assertion is the projective-automorphism theorem for one differential indeterminate:
differential order additivity applied to an automorphism and its inverse forces order zero, and the
ordinary automorphisms of `C(q)` are `PGL_2(C)`.

## Positive content of the scalar no-go

`[NO-GO]` No scalar stable core, scalar Kähler line, scalar gauge torsor, or scalar completion can
carry a positive reversible clock interval.  Adding topology to a single scalar does not repair
this algebraic obstruction.

`[POSITIVE THEOREM]` Rank two is a sharp phase transition.  Persistence and accessibility are
independent invariants: `(3)` says that no information is lost, while `(5)` says that the same
information escapes every fixed finite jet window.  Hypertranscendental constraint topology is
therefore intrinsically multi-observable.

This is the first exact model in the program in which infinite algebraic clock capacity is
concentrated at a boundary by reversible displacement rather than erasure, finite holonomy, or a
chosen analytic completion.

## Affine-building form

The substitution matrix is

```text
A(D)=[[0,1],[1,D]],              det A=-1.                (7)
```

Over the derivative-frequency local field `C((D^(-1)))`, compare the standard lattice

```text
L_0=C[[D^(-1)]]^2
```

with `L_n=A(D)^n L_0`.  The recurrence `(6)` gives pole order `n` in one direction.  Since the
determinant has valuation zero, the two elementary divisors sum to zero.  Thus the relative Cartan
coweight is

```text
(n,-n)                                                   (8)
```

up to the sign convention for the valuation.  Formula `(5)` identifies its positive component
with exact finite-jet reconstruction cost.  This is a literal interval of source-defined lattices,
not a topology selected after inspecting a spectrum.

## External novelty gate

The external gate is against literature, not against other results in this project.

Established parents include:

- reversible and algebraic cellular automata, including finite propagation and inverse-neighbourhood
  growth;
- Laurent/polynomial matrix dynamics and Lyapunov spectra;
- Cartan decomposition and relative position of lattices in affine Grassmannians and
  Bruhat--Tits buildings;
- degree growth and algebraic entropy for birational transformations.

Those parents kill any claim that `(6)`, polynomial-matrix propagation, or `(8)` alone is new.  A
targeted exact-statement search located no source which:

1. separates stable-core persistence from finite-jet accessibility in a free differential field;
2. proves the scalar/rank-two phase transition above;
3. identifies affine-building relative position with exact HT reconstruction order.

The theorem package is therefore a candidate new result, not a priority claim.  Specialist,
MathSciNet, and Zentralblatt review remain required.

## Anti-theatre gate

- `[PASS]` Exact theorem, exact proof, and exact falsifier.
- `[PASS]` The scalar no-go has a strict positive successor at the minimal possible rank.
- `[PASS]` The theorem separates two invariants previously conflated by every scalar model.
- `[FAIL if oversold]` The recurrence and affine-building parent theory are not new.
- `[SIGNIFICANCE]` This is a founding phase-transition theorem and a paper-level result, not by
  itself a Fields-Medal result.  The medal-scale claim is the nonlinear completeness conjecture in
  `nonlinear-hypertranscendental-clock-building-completeness.md`.

## Lean formalization

`GaloisForLFunctions.HTGeometry.DifferentialIndependentObservableNet` now contains:

```text
differentialFamilyObservableField_deriv_mem_succ
clockShearForward
clockShearBackward
clockShearForward_backward
clockShearBackward_forward
clockShearBackwardFirst_add_two
clockShearBackwardFirst_sub_leading_mem
clockShearBackwardFirst_mem_succ
clockShearBackwardFirst_not_mem_self
clockShearBackwardFirst_mem_iff
```

The last theorem is the exact iff `(5)`.  The touched module passed direct Lean checking with no
warnings.  No Lake build was run because its `.olean` dependency cache already existed.

## RH pressure test only

The theorem implies that any proposed common obstruction object assembled from scalar zeta alone
has insufficient algebraic rank to carry nonzero reversible clock displacement.  A viable
realization must contain at least two transverse source observables and prove that their coupling
is source-canonical.  Prime/archimedean or source/reflection pairs are possible candidates, but no
such identification is asserted here and there is no RH consequence.

## Gates

- [x] 0 -> 1: exact rank threshold and falsifier isolated
- [x] 1 -> 2: complete paper proof
- [x] 2 -> 3: exact reconstruction iff Lean-formalized
- [ ] 3 -> 4: independent specialist novelty review and standalone preprint

