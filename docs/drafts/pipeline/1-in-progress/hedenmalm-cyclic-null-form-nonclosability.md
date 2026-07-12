# Hedenmalm cyclic-null positive forms are forced to be nonclosable

- **ID:** `hedenmalm-cyclic-null-form-nonclosability`
- **Stage:** 1-in-progress
- **Type:** THEOREM PACKAGE / HILBERT--POLYA TOPOLOGY CLASSIFICATION
- **Scientific status:** `[PAPER PROOF COMPLETE] [LEAN COMPLETE] [NOVELTY UNVERIFIED] [NOT AN RH PROOF]`
- **Formal modules:**
  - `formal/GaloisForLFunctions/RHTower/CyclicNullFormNonclosability.lean`
  - `formal/GaloisForLFunctions/RHTower/XiThetaSchwartzL2Nonclosability.lean`
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

## 2. Cyclic-null theorem `[PROVED ON PAPER AND IN LEAN]`

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

## 3. Hedenmalm specialization `[PROVED ON PAPER AND IN LEAN]`

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

for every `t` and Schwartz vector `w`.  Applying `(3)`--`(5)` proves:

> Every nonzero nonnegative Hedenmalm source-core form is nonclosable in ordinary `L²(R)`.

Equivalently, inside the nonnegative, momentum-symmetric, theta-null cone, the ordinary-`L²`
sequentially closable locus is exactly the zero form:

```text
q sequentially L²-closable
  iff q(u,v)=0 for every pair of Schwartz vectors u,v.    (7b)
```

This is a complete closure classification rather than only a no-go statement.  A nonzero
orientation is forced to choose a topology singular to ordinary `L²`; there is no intermediate
closable positive source form.

The proved statement is stronger at the radical level.  If `N_q` is the left radical in Schwartz
space and `j` is the ordinary `L²` inclusion, then every nonzero momentum-symmetric theta-null
form satisfies

```text
closure(j(N_q))=L²(R),
j(N_q) != L²(R),
j(N_q) is not closed.                                    (7a)
```

Thus the physical `L²` topology sees a proper metric-null subspace as dense.  Positivity is needed
only to promote this dense-proper radical geometry to the fixed-positive-energy nonclosability
sequence `(5)`.

The density statement has an exact quotient consequence.  For every Schwartz vector `u` and
every `epsilon>0`, there is a radical vector `r` with

```text
norm_L²(u-r)<epsilon.                                    (7c)
```

Hence the quotient seminorm induced from ordinary `L²` is identically zero on the whole oriented
source quotient.  The required singular topology must therefore create its separation from
divisor/source data; it cannot be a strengthening obtained by closing a nonzero ordinary-`L²`
quadratic form.

Equivalently, no positive self-adjoint metric operator and no closed nonnegative quadratic form on
ordinary `L²(R)` can realize the Hedenmalm orientation while retaining the translation-stable
theta source core.

## 4. Relation to moment determinacy and orientation

The pointed all-order moment germ already determines the analytic theta source, `XiC`, and the
local Hedenmalm--de Branges Bezoutian.  It does not determine the sign of that Bezoutian.  The
present theorem proves the positive carrier law

```text
all-order pointed moments determine the kernel;
nonzero positive orientation forces an L²-singular, nonclosable completion. (8)
```

Thus more moments cannot replace the missing topology.  A successful construction must orient the
unique reconstructed kernel on a singular divisor/trace rigging or another source-defined Hilbert
space not closable through ordinary `L²`.

## 5. Gates

- [x] define the exact sequential closability predicate;
- [x] prove the abstract cyclic-null nonclosability theorem;
- [x] prove a left-radical vector of a Hermitian form lies in the right radical;
- [x] lift algebraic orbit-span approximants through the source embedding;
- [x] instantiate the theorem for the actual normalized theta source;
- [x] prove that the ordinary-`L²` radical image is dense, proper, and nonclosed;
- [x] prove that every source coset has zero ordinary-`L²` quotient seminorm;
- [x] produce the fixed-positive-energy `L²`-null sequence;
- [x] classify the entire ordinary-`L²` closable cone: it consists exactly of the zero form;
- [x] exact Lean build and axiom audit;
- [ ] parent-theory and primary-literature audit;
- [ ] significance score at or above the publication gate.

## 6. Preliminary literature boundary

Kato's standard sequence criterion supplies the parent notion of closability, and the abstract
cyclic-null singular-sequence argument is elementary quadratic-form theory.  Hedenmalm's June 2026
paper constructs the theta differential pair and asks for related sesquilinear forms on the finite
eigenfunction span, but it does not identify the normalized theta source as translation-cyclic in
ordinary `L²`, discuss closability, or derive dense radical and zero quotient-seminorm conclusions.
Targeted searches have not located the exact Hedenmalm specialization.  This supports provisional
novelty of the application, not yet a completed literature-wide novelty certificate.

## 7. Attack boundary

1. The abstract theorem is a standard quadratic-form argument and is therefore a bridge unless the
   exact singular-sequence strengthening has an unrecognized parent.
2. The Hedenmalm specialization may be new because the parent preprint does not identify its theta
   source as an ordinary-translation cyclic null vector.
3. Nonclosability does not prove the missing Bezoutian sign and therefore does not prove RH.
4. The theorem does not exclude singular divisor-supported or rigged-Hilbert-space metrics; it
   forces precisely that architecture.
