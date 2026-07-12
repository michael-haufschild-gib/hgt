# Hedenmalm cyclic-null positive forms are forced to be nonclosable

- **ID:** `hedenmalm-cyclic-null-form-nonclosability`
- **Stage:** 1-in-progress
- **Type:** THEOREM PACKAGE / HILBERT--POLYA TOPOLOGY CLASSIFICATION
- **Scientific status:** `[CONJECTURE] [PROOF TARGET] [NOVELTY UNVERIFIED] [NOT AN RH PROOF]`
- **Claim:** Every nonzero nonnegative momentum-symmetric sesquilinear form on the Hedenmalm
  Schwartz source domain which annihilates the normalized theta source fails sequential
  closability in ordinary `L²(R)`.  More precisely, it admits an `L²`-null sequence whose pairwise
  differences have zero form energy while every term has one fixed positive form energy.

## 1. Sequential closability

Let `E` be a complex vector space, `H` a complex Hilbert space, `j:E->H` a linear source
embedding, and `q` a nonnegative sesquilinear form on `E`.  Call `q` sequentially closable through
`j` if every sequence `(u_n)` satisfying

```text
j(u_n) -> 0 in H,
q(u_n-u_m,u_n-u_m) -> 0 as n,m -> infinity              (1)
```

also satisfies

```text
q(u_n,u_n) -> 0.                                         (2)
```

For nonnegative forms on a dense Hilbert subspace, this is the standard sequential criterion for
closability.

## 2. Cyclic-null theorem `[CONJECTURE; PROOF TARGET]`

Let `(v_t)` be a family in `E` such that

```text
closure span{j(v_t)}=H,
q(v_t,w)=0 for every t and w.                             (3)
```

If there is `u in E` with `q(u,u)>0`, then density supplies a sequence `r_n` in the algebraic span
of the `v_t` with

```text
j(r_n) -> j(u).                                          (4)
```

Every `r_n` lies in the radical of `q`.  Therefore `u_n=u-r_n` obeys

```text
j(u_n) -> 0,
q(u_n-u_m,u_n-u_m)=0,
q(u_n,u_n)=q(u,u)>0                                      (5)
```

for all `n,m`.  This contradicts sequential closability.  The proof uses only algebraic span,
cyclicity, and positivity; it does not use a spectral theorem.

## 3. Hedenmalm specialization `[CONJECTURE; PROOF TARGET]`

Take

```text
E=Schwartz(R),
H=L²(R),
j=the canonical inclusion,
k(x)=2 VarTheta_00(i exp(2x)).                            (6)
```

The formal corpus proves unconditionally that the complete translation orbit of `k` is cyclic in
`L²(R)`.  Momentum symmetry makes `q` invariant under simultaneous translation, and theta
nullity gives

```text
q(T_t k,w)=0                                             (7)
```

for every `t` and Schwartz vector `w`.  Applying `(3)`--`(5)` should prove:

> Every nonzero nonnegative Hedenmalm source-core form is nonclosable in ordinary `L²(R)`.

Equivalently, no positive self-adjoint metric operator and no closed nonnegative quadratic form on
ordinary `L²(R)` can realize the Hedenmalm orientation while retaining the translation-stable
theta source core.

## 4. Relation to moment determinacy and orientation

The pointed all-order moment germ already determines the analytic theta source, `XiC`, and the
local Hedenmalm--de Branges Bezoutian.  It does not determine the sign of that Bezoutian.  The
present claim would prove the positive carrier law

```text
all-order pointed moments determine the kernel;
nonzero positive orientation forces an L²-singular, nonclosable completion. (8)
```

Thus more moments cannot replace the missing topology.  A successful construction must orient the
unique reconstructed kernel on a singular divisor/trace rigging or another source-defined Hilbert
space not closable through ordinary `L²`.

## 5. Gates

- [ ] define the exact sequential closability predicate;
- [ ] prove the abstract cyclic-null nonclosability theorem;
- [ ] prove a null vector of a nonnegative sesquilinear form lies in both radicals;
- [ ] lift algebraic orbit-span approximants through the source embedding;
- [ ] instantiate the theorem for the actual normalized theta source;
- [ ] produce the fixed-positive-energy `L²`-null sequence;
- [ ] exact Lean build and axiom audit;
- [ ] parent-theory and primary-literature audit;
- [ ] significance score at or above the publication gate.

## 6. Attack boundary

1. The abstract theorem is expected to be a standard quadratic-form argument and is therefore a
   bridge unless the exact singular-sequence strengthening has an unrecognized parent.
2. The Hedenmalm specialization may be new because the parent preprint does not identify its theta
   source as an ordinary-translation cyclic null vector.
3. Nonclosability does not prove the missing Bezoutian sign and therefore does not prove RH.
4. The theorem does not exclude singular divisor-supported or rigged-Hilbert-space metrics; it
   forces precisely that architecture.
