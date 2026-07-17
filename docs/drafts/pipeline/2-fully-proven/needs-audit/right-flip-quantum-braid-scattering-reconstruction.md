# Right-flip quantum--braid scattering reconstruction

- **ID:** HT-QFT-RIGHT-FLIP-RECONSTRUCTION
- **Stage:** 2-fully-proven / needs-audit
- **Type:** THEOREM (paper)
- **Source:** independent convention audit of Lechner--Schuetzenhofer and twisted Araki--Woods reconstruction
- **Statement:** The adjacent-braid input `B` reconstructs the physical quantum two-particle matrix `R = B F` on the ordered rapidity chamber; all load-bearing axioms, including the fermionic zero and crossing, transport exactly through this right flip.

## Goal

Remove the convention obstruction between a physical quantum two-particle matrix and the
adjacent Yang--Baxter operator used to define an `S`-symmetric or twisted Fock space.  The
result must identify the matrix actually recovered by Haag--Ruelle scattering rather than
relying on the name assigned to the input matrix.

## Theorem [PROVED HERE]

Let `K` be a finite-dimensional complex Hilbert space, let
`F : K ⊗ K → K ⊗ K` be the tensor flip, and let `B(θ)` be a unitary
operator-valued function satisfying the adjacent spectral Yang--Baxter equation

```text
B12(x) B23(x+y) B12(y) = B23(y) B12(x+y) B23(x).           (1)
```

Define the right-flip quantum matrix

```text
R(θ) := B(θ) F,             equivalently B(θ)=R(θ)F.       (2)
```

Then:

1. `(1)` is equivalent to the quantum spectral Yang--Baxter equation

   ```text
   R12(x) R13(x+y) R23(y) = R23(y) R13(x+y) R12(x).        (3)
   ```

2. `B(0)=-I` is equivalent to the physical fermionic anchor `R(0)=-F`.
3. `B(θ)` is unitary if and only if `R(θ)` is unitary.
4. The adjacent hermitian-analyticity axiom

   ```text
   B(-θ)=B(θ)*
   ```

   is equivalent to

   ```text
   R(-θ)=F R(θ)* F.                                    (4)
   ```

5. Let `J` be the internal charge conjugation.  The standard-subspace crossing boundary
   condition for the braid input,

   ```text
   ⟨v2⊗v1, B(t+iπ)(v4⊗v3)⟩
     = ⟨v1⊗Jv4, B(-t)(v3⊗Jv2)⟩,                         (5)
   ```

   is equivalent to the physical quantum condition

   ```text
   ⟨v2⊗v1, R(t+iπ)(v3⊗v4)⟩
     = ⟨v1⊗Jv4, R(-t)(Jv2⊗v3)⟩.                         (6)
   ```

6. In the Lechner--Schuetzenhofer scattering theorem, the reconstructed two-particle
   scattering operator on the fundamental chamber `θ1 ≤ θ2` has matrix elements

   ```text
   Sscat(θ1,θ2)^{a1 a2}_{b1 b2}
      = B(θ2-θ1)^{a1 a2}_{b2 b1}
      = R(θ2-θ1)^{a1 a2}_{b1 b2}.                    (7)
   ```

   Thus the construction reconstructs `R=B F`, not the bare matrix `B`.  The other rapidity
   chamber is the Bose-symmetric continuation of this fundamental-chamber multiplier.

## Proof

Write `Fi=F_{i,i+1}`.  Substituting `B12=R12 F12` and `B23=R23 F23` into the left side of
`(1)` and moving the flips to the right gives

```text
R12(x) R13(x+y) R23(y) F12 F23 F12.
```

The right side becomes

```text
R23(y) R13(x+y) R12(x) F23 F12 F23.
```

Since the flips obey the braid relation, cancellation proves the equivalence with `(3)`.
Items 2 and 3 follow immediately from `F*=F=F^{-1}`.  For item 4,

```text
R(-θ)F = B(-θ) = B(θ)* = F R(θ)*,
```

and right multiplication by `F` yields `(4)`.  In `(5)`, replacing `B` by `RF` changes
the two input tensors `v4⊗v3` and `v3⊗Jv2` into `v3⊗v4` and `Jv2⊗v3`,
respectively, proving `(6)`.

Finally, the published two-particle scattering formula reverses the two lower indices of
the adjacent input matrix.  But

```text
(B F)^{a1 a2}_{b1 b2}=B^{a1 a2}_{b2 b1},
```

so its ordered-chamber multiplier is exactly `R`.  This proves `(7)`.

## The `O(N)` convention conflict is resolved

The earlier Lechner--Schuetzenhofer construction uses the adjacent input

```text
B_N(θ)=σ1(θ)K+σ2(θ)F+σ3(θ)I,            B_N(0)=-I.
```

Because `K F=K` and `F²=I`, its reconstructed physical quantum matrix is

```text
R_N(θ)=B_N(θ)F
        =σ1(θ)K+σ2(θ)I+σ3(θ)F,               R_N(0)=-F,
```

which is precisely the standard physical `O(N)` coefficient order.  The later
Alazzawi--Lechner text displays `R_N` while imposing the adjacent equation intended for
`B_N`; the earlier source and the scattering formula together identify the missing right
flip.

## Physical consequence for projective HT

A physical intrinsically mixing projective-HT quantum matrix `R` should be searched for on
the quantum surface `(3)`, with zero `-F` and crossing `(6)`.  Its Fock-space braid input is
`B=R F`, which has zero `-I`.  The identity-zero Pauli trace theorem therefore applies to
the correct construction convention.  No separate transformed-crossing or transformed
wedge-locality axiom is needed: `(5)` and `(6)` are the same condition under the right flip.

The remaining construction problem is the all-particle bounded analytic intertwiner into
the identity-zero invariant subspace.  It is not a convention problem.

## Anti-theatre attacks

1. **A standard braid/quantum conversion presented as new physics.**  Items 1--5 are
   elementary transport identities.  The potentially new content is the exact repair of
   the published reconstruction convention and its consequence for the identity-zero
   locality problem; this still requires a literature novelty audit.
2. **Calling `B` or `R` physical by notation.**  Rejected.  Equation `(7)` identifies the
   reconstructed multiplier operationally.
3. **Using the left flip `F B` without parity invariance.**  Rejected.  Scattering reverses
   the incoming lower indices and therefore selects the right flip `B F`.  The two agree
   only when the matrix commutes with `F`.
4. **Claiming a full compact-local theory.**  Rejected.  The identity-zero analytic
   intertwiner remains open.

## Novelty and significance gates

The significance gate is passed: this theorem reconnects standard physical nonabelian
quantum matrices, including the `O(N)` example, to the adjacent-braid Fock construction and
shows that the identity-zero modular-nuclearity theorem addresses the correct sector.

The novelty gate remains open.  The braid/quantum equivalence itself is standard.  A
focused primary-literature audit must determine whether the right-flip reconstruction and
the resulting correction of the later `O(N)` convention have already been stated explicitly.

## Exact open core

1. Audit primary literature for an explicit `R=B F` reconstruction statement or erratum.
2. Construct an all-particle bounded analytic intertwiner for `B(0)=-I`.
3. Combine that intertwiner with the proved componentwise-Pauli trace theorem.
4. Construct a positive-unitary, crossing-symmetric, intrinsically mixing projective-HT
   solution of `(3)`.
5. Formalize the finite-dimensional algebraic content of items 1--4 in `HTGeometry`.

## Primary literature

- G. Lechner and C. Schuetzenhofer, *Towards an Operator-Algebraic Construction of
  Integrable Global Gauge Theories*, <https://arxiv.org/abs/1208.2366>.
- S. Alazzawi and G. Lechner, *Inverse Scattering and Locality in Integrable Quantum Field
  Theories*, <https://arxiv.org/abs/1608.02359>.
- R. Correa da Silva and G. Lechner, *Modular Structure and Inclusions of Twisted
  Araki--Woods Algebras*, <https://arxiv.org/abs/2212.02298>.
- G. Lechner, *Twisted Araki--Woods Algebras, the Yang--Baxter Equation, and Quantum Field
  Theory*, <https://arxiv.org/abs/2311.14610>.

## Gates

- [x] 0 → 1 in-progress: well-posed, source-pure, attack idea
- [x] 1 → 2 fully-proven: complete paper proof, `[PROVED HERE]`, no open dependency
- [ ] literature novelty audit
- [ ] 2 → 3 formalized: unconditional Lean theorem in `HTGeometry`
- [ ] 3 → 4 publication-ready

## Log

- 2026-07-17 — paper proof completed after tracing the two-particle scattering formula rather than source notation.
