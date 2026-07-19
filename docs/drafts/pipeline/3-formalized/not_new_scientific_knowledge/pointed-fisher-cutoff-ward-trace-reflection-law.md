# Pointed Fisher cutoff Ward-trace reflection law

- **ID:** `pointed-fisher-cutoff-ward-trace-reflection-law`
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Scientific status:** `[PROVED HERE] [NEW INTERNAL CONNECTION] [NOT CLAIMED NOVEL] [PROOF-CONTRIBUTING]`
- **Parents:** the finite-rank pointed Fisher connection; the Burnol conductor-reflection law;
  finite-rank trace cyclicity.
- **Statement:** A bounded, possibly noncompact cutoff edge has a canonical signed pairing with
  the rank-two pointed Fisher connection; the pairing is exactly an adjoint double-commutator
  value and is invariant under cutoff complementation and unitary reflection.

## Goal

The Burnol conductor edge is bounded but is not expected to be Hilbert--Schmidt.  Consequently its
ordinary Hilbert--Schmidt energy is the wrong scalar interface.  The goal is to couple that edge to
the existing finite-rank Fisher source without imposing compactness and without squaring away its
orientation.  This supplies a source-facing scalar that can be transported across the physical /
Fourier reflection, while leaving the genuinely open prime--Gamma incidence theorem explicit.

## Gates

- [x] 0 → 1  in-progress: well-posed, source-pure, attack idea, Door passport sketch
- [x] 1 → 2  fully-proven: complete paper proof, `[PROVED HERE]`, no open dependency
- [x] 2 → 3  formalized: Lean theorem, narrow module build green, axioms audited
- [ ] 3 → 4  publication-ready: standalone paper (theorem + proof + Lean certificate + Door-2)

## Statement

Let `H` be a complex Hilbert space, let `P,T : H -> H` be arbitrary bounded operators, and let
`psi,chi : H`.  Define the normalized pointed Fisher connection

```text
F(psi,chi) = 2^(-1/2) (|chi><psi| + |psi><chi|),
K_P(T)     = [T,P],
D*_P(T)    = [[T,P],P^*].
```

The **pointed cutoff Ward trace** is

```text
W_P(T;psi,chi) = Tr([F(psi,chi),P]^* [T,P]).             (1)
```

The trace in `(1)` is canonical even when `[T,P]` is noncompact: the first factor is finite rank.
Then

```text
W_P(T;psi,chi)
  = Tr(F(psi,chi) D*_P(T))
  = 2^(-1/2) (
      <psi,D*_P(T)chi> + <chi,D*_P(T)psi>).              (2)
```

For a self-adjoint cutoff, `D*_P(T)=D_P(T)=[[T,P],P]`, recovering the ordinary double cutoff
commutator used by the projection calculus.

The pairing retains tangent orientation:

```text
W_P(T;psi,-chi) = -W_P(T;psi,chi).                       (O)
```

This is the formal distinction from the quadratic Hilbert--Schmidt energy, which is even under
the same sign reversal.

It has two exact reflection laws:

```text
W_(1-P)(T;psi,chi) = W_P(T;psi,chi),                     (3)
W_(JPJ)(JTJ;Jpsi,Jchi) = W_P(T;psi,chi)                  (4)
```

whenever `J^*=J` and `J^2=1`.  If additionally `JTJ=T`, as for the bounded Burnol conductor
algebra, `(4)` transports the signed conductor--Fisher value between the physical and reflected
Fourier cutoffs without changing `T`.

The value is additive in the bounded channel.  Consequently an arbitrary position channel `M`
has the exact hypothesis-free Lüders/Burnol split

```text
W_(JPJ)(M;Jpsi,Jchi)
  = W_P(H(M_0,J);psi,chi)
    + W_(JPJ)(M_off;Jpsi,Jchi),                          (S)

M_0   = P M P + (1-P)M(1-P),
M_off = (1-P)MP + PM(1-P),
H(M_0,J) = M_0 + J M_0 J.
```

Here `M_0` commutes with `P` by idempotence, so the first term follows from Burnol cancellation;
the second term is the exact, explicit failure of the original channel to commute with the
physical cutoff.  No commutation premise on `M` is hidden or discarded.

## Proof

For bounded `A,B` and vectors `x,y`, the rank-one trace identity is

```text
Tr(A |x><y| B) = <y, B A x>.                             (5)
```

Indeed `A |x><y| B = |Ax><B^*y|`, and Parseval gives
`Tr(|u><v|)=<v,u>`.  Thus all traces below are absolutely convergent finite-rank traces, with no
trace-class premise on `A` or `B`.

Self-adjointness of `F` gives, for an arbitrary bounded cutoff,

```text
[F,P]^* = P^*F-FP^*.                                    (6)
```

Write `K=[T,P]`.  Applying `(5)` to each of the two rank-one summands of `F` permits cyclic passage
across the finite-rank factor:

```text
Tr(P^* F K) = Tr(F K P^*).                              (7)
```

Therefore

```text
Tr([F,P]^* K)
  = Tr((P^* F - F P^*)K)
  = Tr(F(KP^*-P^*K))
  = Tr(F [[T,P],P^*]),                                  (8)
```

which is the first equality in `(2)`.  Applying `(5)` to `F D*_P(T)` gives the second equality.

For `(3)`, both commutators in `(1)` change sign under `P -> 1-P`; the adjoint and product therefore
leave `(1)` unchanged.  Equivalently, `D*_(1-P)(T)=D*_P(T)`.

For `(4)`, involutivity gives the covariance laws

```text
[JXJ,JYJ] = J[X,Y]J,
D*_(JPJ)(JTJ) = J D*_P(T) J.                            (9)
```

Self-adjointness of `J`, together with `J^2=1`, gives
`<Jx,Jy>=<x,y>`.  Apply the value formula `(2)` to `(9)` to obtain `(4)`.

## Hostile novelty and significance audit

The rank-one trace identity, cyclic transgression, and unitary covariance are standard operator
algebra; this card does **not** claim a new general theorem in operator theory.  The project-level
advance is the exact weld of three previously separate interfaces:

1. the finite-rank pointed Fisher source, which retains tangent orientation;
2. the bounded but noncompact Burnol cutoff edge;
3. the physical/Fourier conductor reflection.

This is not an RH theorem and not a completed-source identification.  It does remove the false
Hilbert--Schmidt requirement from the local polarized pairing and, unlike a squared norm, does not
erase the sign of the source tangent.  The remaining scientific theorem is still the construction
of the prime--Gamma/Sonin incidence carrying the arithmetic Fisher tangent into this conductor
pairing, followed by the one-sided completed-source comparison.

## Relation to the retired scalarization

The failed Möbius--Fisher/Sonin lift showed that positive Gram or Hilbert--Schmidt energies erase
the Möbius orientation.  Equation `(1)` is the strongest positive survivor of that obstruction:
it is bilinear and signed, but remains finite because only the Fisher probe, not the conductor edge,
must be finite rank.  No claim is made that the missing incidence map exists or that `(1)` already
equals the completed von Mangoldt--Gamma source.

## Literature boundary

- J.-F. Burnol, *The Explicit Formula and the conductor operator*, arXiv:math/9902080.
- J.-F. Burnol, *Spectral Analysis of the local Conductor Operator*, arXiv:math/9811040.
- A. Connes and C. Consani, *The Scaling Hamiltonian*, arXiv:1910.14368.

These sources establish the conductor/explicit-formula and cutoff-trace parent setting.  The
finite-rank Ward transgression above is elementary; external novelty is neither needed nor claimed.

The paper proof initially assumed `T^*=T` and `P^*=P`.  Formal dependency minimization showed that
neither hypothesis is needed: the unconditional curvature is `[[T,P],P^*]`.  Self-adjointness of
`P` is now only the specialization identifying this with the ordinary double commutator.

## Log

- 2026-07-19 — paper proof completed after rejecting Hilbert--Schmidt scalarization of the
  noncompact conductor edge; queued for narrow Lean formalization.
- 2026-07-19 — formalized in
  `HTGeometry/PointedFisherCutoffWardTrace.lean` and
  `RHTower/SoninBurnolPointedWardTrace.lean`; exact targeted modules compile cleanly.
- 2026-07-19 — dependency minimization removed self-adjointness of the bounded channel; Lean also
  certifies tangent oddness as `pointedCutoffWardTrace_neg_tangent`.
- 2026-07-19 — channel additivity and the exact arbitrary-channel Lüders/Burnol residual split
  formalized as `pointedCutoffWardTrace_add` and
  `pointedCutoffWardTrace_evenFourierPosition_ludersBoundarySplit`.
- 2026-07-19 — the cutoff self-adjointness premise was eliminated by lifting the law to
  `cutoffWardAdjointCurvature`; the Burnol reflection and Lüders split now require no cutoff
  adjointness hypothesis.
