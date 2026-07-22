# Boundary-channel completion for every finite CCM Weil matrix

- **ID:** `ccm-boundary-channel-completion-trichotomy`
- **Stage:** 2-fully-proven
- **Type:** UNIVERSAL THEOREM / FINITE CCM OBSTRUCTION CLOSURE
- **Scientific status:** `[PROVED HERE] [CANDIDATE NEW SCIENTIFIC KNOWLEDGE]`
  `[EXTERNAL NOVELTY AUDIT OPEN] [NOT AN RH PROOF]`
- **Parent sources:** Connes--Consani--Moscovici, *Zeta Spectral Triples*, Lemma 5.1;
  Connes--van Suijlekom, *Quadratic Forms, Real Zeros and Echoes of the Spectral Action*,
  Section 5.
- **Statement:** The simple-even hypothesis is not needed to construct a self-adjoint finite CCM
  clock.  Every positive-semidefinite reflection-graded rank-two displacement matrix has exactly
  one of three boundary channels.  In every channel an explicit rank-one correction of the clock
  descends to a self-adjoint operator on the full radical quotient.  For a simple radical, either
  the published even transform or a new odd weighted transform is real-rooted.

## The open question closed by this theorem

For the finite truncated Weil form, CCM assume that its lowest eigenvalue is simple and that the
ground vector is even.  This assumption is used to correct the finite scaling clock by one rank-one
operator and to prove that the resulting quotient clock is self-adjoint.  General matrices with
the same displacement structure can have an odd or multiple ground space, so the assumption cannot
be proved from displacement alone.

The theorem below replaces that assumption rather than hiding it.  Given the actual truncated Weil
matrix `Q_(lambda,N)`, subtract its lowest eigenvalue and apply the theorem.  This works for every
`lambda,N`, with no sign, simplicity, parity, zeta-zero, or asymptotic hypothesis.  Thus finite
self-adjoint spectral-triple existence is unconditional.  What remains open is identifying a
cofinal branch whose normalized determinant converges divisor-preservingly to `Xi`.

## Abstract CCM displacement system

Let `V` be a finite-dimensional real Hilbert space.  Let `T,D,Gamma` be self-adjoint operators and
let `eta,beta in V` satisfy

```text
Gamma^2=I,        Gamma T=T Gamma,       Gamma D=-D Gamma,
Gamma eta=eta,    Gamma beta=-beta,
D T-T D=|beta><eta|-|eta><beta|.                         (1)
```

Assume `T>=0` and put `K=ker T`.  In the CCM application,

```text
T=Q_(lambda,N)-epsilon_(lambda,N) I,
D e_j=j e_j,       eta=sum_j e_j,       beta=sum_j b_j e_j. (2)
```

The quotient `V/K` has the positive-definite inner product

```text
<[x],[y]>_T=<T x,y>.                                      (3)
```

Write `K_+` and `K_-` for the two reflection parities in `K`.

## Theorem: boundary-channel trichotomy and quotient completion

Exactly one of the following mutually exclusive cases holds.

### E. Active even boundary

`eta|K` is nonzero.  Then `beta` is orthogonal to all of `K`.  Choose `e in K_+` with
`<eta,e>=1` and define

```text
A_E=D-|D e><eta|.                                         (4)
```

Then

```text
A_E K subset K,       T A_E=A_E^* T,       A_E e=0.       (5)
```

### O. Active odd boundary

`beta|K` is nonzero.  Then `eta` is orthogonal to all of `K`.  Choose `o in K_-` with
`<beta,o>=1` and define

```text
A_O=D-|D o><beta|.                                        (6)
```

Then

```text
A_O K subset K,       T A_O=A_O^* T,       A_O o=0.       (7)
```

### N. Neutral boundary

Both `eta` and `beta` are orthogonal to `K`.  Therefore both lie in `range T`.  Let
`y=T^dagger beta` be the Moore--Penrose solution in `K^perp` and define

```text
A_N=D+|y><eta|.                                            (8)
```

Then

```text
A_N K subset K,       T A_N=A_N^* T.                      (9)
```

In all three cases the induced operator `bar A` on `(V/K,<,>_T)` is self-adjoint.  Consequently
its characteristic polynomial has only real zeros.

## Proof

For `v in K`, applying `(1)` gives the universal radical transport identity

```text
T Dv=-beta <eta,v>+eta <beta,v>.                           (10)
```

If the even channel is active, choose `e` as above.  Equation `(10)` gives `TDe=-beta`.  Since
`T` is self-adjoint, `range T=K^perp`; hence `beta` is orthogonal to `K`.  For every `v in K`,

```text
T A_E v
 =T Dv-TDe <eta,v>
 =-beta <eta,v>+beta <eta,v>=0,
```

so `A_E` preserves `K`.  Moreover, using `TD-DT=|eta><beta|-|beta><eta|`,

```text
T A_E-A_E^*T
 =(TD-DT)-|TDe><eta|+|eta><TDe|
 =(|eta><beta|-|beta><eta|)
   +|beta><eta|-|eta><beta|=0.                            (11)
```

Also `A_E e=De-De<eta,e>=0`.  This proves `(5)`.

The odd case is dual.  Equation `(10)` gives `TDo=eta`, hence `eta perpendicular K`, and

```text
T A_O-A_O^*T
 =(TD-DT)-|eta><beta|+|beta><eta|=0.                      (12)
```

The same substitution in `(10)` proves `A_O K subset K`, and the normalization gives `A_Oo=0`.
The two active cases cannot coexist because either active case puts the opposite boundary vector
in `K^perp`.

In the neutral case, `Ty=beta` and both boundary functionals vanish on `K`.  Thus `(10)` gives
`DK subset K`, so `A_NK subset K`.  Finally,

```text
T A_N-A_N^*T
 =(TD-DT)+|beta><eta|-|eta><beta|=0.                      (13)
```

This proves the trichotomy and every completion identity.  If `A` preserves `K` and
`TA=A^*T`, then

```text
<bar A[x],[y]>_T=<TAx,y>=<Tx,Ay>=<[x],bar A[y]>_T,
```

so `bar A` is self-adjoint in the positive quotient metric `(3)`.

## Simple radical: parity-dual real-zero law

Assume `K=R xi`.  Since `K` is reflection-invariant, `xi` is even or odd.

The neutral case is impossible.  Indeed, if both boundary pairings vanished, `(10)` would make
`Dxi` lie in the one-dimensional radical.  But `D` reverses parity, so `Dxi=0`; in the CCM clock
the kernel of `D` is the even central vector `e_0`, which has `<eta,e_0>=1`.  This contradicts
neutrality.

If `xi` is even, normalize `<eta,xi>=1`.  The matrix determinant lemma applied to `(4)` gives

```text
det(A_E-zI)
 =-z det(D-zI) <eta,(D-zI)^(-1)xi>.                       (14)
```

Since `A_E xi=0`, the characteristic polynomial of the self-adjoint quotient is, up to a nonzero
constant,

```text
P_E(z)=det(D-zI)<eta,(D-zI)^(-1)xi>.                       (15)
```

This is CCM's polynomial and therefore the Fourier-transform numerator of the even ground vector.

If `xi` is odd, normalize `<beta,xi>=1`.  The same calculation applied to `(6)` gives

```text
det(A_O-zI)
 =-z det(D-zI) <beta,(D-zI)^(-1)xi>,                      (16)

P_O(z)=det(D-zI)<beta,(D-zI)^(-1)xi>.                     (17)
```

Both `P_E` and `P_O` have only real zeros because they are quotient characteristic polynomials.
For the CCM diagonal clock, `(17)` is explicitly

```text
P_O(z)=sum_(j=-N)^N b_j xi_j product_(k!=j)(k-z).          (18)
```

Thus odd ground parity does not destroy the finite real-spectrum construction.  It switches the
canonical boundary observable from the Dirichlet vector `eta` to the displacement vector `beta`.

## Universal law and significance

The theorem is a boundary-channel analogue of limit-point/limit-circle classification:

```text
radical touches even boundary  -> eta-completion,
radical touches odd boundary   -> beta-completion,
radical touches neither        -> pseudoinverse completion. (19)
```

This is not an equivalence criterion for simple-evenness.  It proves that the finite CCM
self-adjointness mechanism survives every possible parity and multiplicity of the true floor.
It therefore closes the first finite construction obstruction stated in *Zeta Spectral Triples*.
It does not prove the second, cofinal source/divisor-transfer obstruction: only the even branch is
currently identified with the prolate `h_0-h_4` seed whose transform tends to `Xi`.

## Novelty audit

Connes--van Suijlekom prove the even one-dimensional case and note that an individual kernel
polynomial need not remain real-rooted when the radical has higher dimension.  Their Appendix B
also exhibits positive displacement matrices with odd kernel vectors.  Neither source states the
odd `beta`-weighted determinant `(17)`, boundary exclusivity, the neutral pseudoinverse branch, or
the all-radical quotient completion.  Targeted corpus and primary-source searches found no such
trichotomy.  Priority remains provisional pending expert review.

## Lean boundary

Formalize the unconditional algebraic core, not an RH-facing wrapper:

1. radical transport `(10)`;
2. active-even exclusivity and completion `(5)`;
3. active-odd exclusivity and completion `(7)`;
4. neutral-source completion `(9)` from an explicit solution `Ty=beta`;
5. the rank-one determinant identities `(14)` and `(16)` when the required matrix-determinant
   infrastructure is available.

The Moore--Penrose existence statement is ordinary finite-dimensional linear algebra; the Lean
core should accept the explicit solution `y` and prove the completion identity without adding an
axiom.

## Gates

- [x] exact source problem identified
- [x] complete paper proof
- [x] odd and multiple radical cases included
- [x] actual finite CCM instantiation is unconditional
- [x] no RH, Xi-zero, asymptotic, or positivity-of-Weil hypothesis
- [ ] independent proof audit
- [ ] external priority audit
- [ ] Lean algebraic core
- [ ] standalone paper draft
- [ ] cofinal branch identification and divisor-preserving transfer to `Xi`

## References

- A. Connes, C. Consani, H. Moscovici, *Zeta Spectral Triples*, arXiv:2511.22755.
- A. Connes, W. D. van Suijlekom, *Quadratic Forms, Real Zeros and Echoes of the Spectral
  Action*, arXiv:2511.23257.

## Log

- 2026-07-22 -- Derived boundary exclusivity directly from the radical transport identity.  Added
  the odd `beta`-weighted real-zero branch and neutral pseudoinverse completion.  This removes
  simple-evenness from finite CCM self-adjoint quotient existence for every truncation.
