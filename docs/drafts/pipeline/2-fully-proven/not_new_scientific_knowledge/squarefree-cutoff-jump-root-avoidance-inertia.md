# Squarefree cutoff jumps have a root-avoidance signature and a hyperbolic complement

- **ID:** `squarefree-cutoff-jump-root-avoidance-inertia`
- **Stage:** 2-fully-proven on paper / not new scientific knowledge
- **Type:** THEOREM / POSITIVE NO-GO CLASSIFICATION
- **Scientific status:** `[PROVED HERE] [SOURCE-SPECIFIC BRIDGE] [EXTERNAL NOVELTY UNVERIFIED]`
  `[NOT AN RH PROOF]`
- **Parents:** `common-profile-boolean-anchor-curvature.md` `(SG1)`--`(SG4)`, Haynsworth inertia
  additivity, finite tensor pencils, and the squarefree two-root CRT survival product.

## Statement

Let `P` be a finite prime set, `Q=prod_(p in P)p`, and let `empty != U subset P`.  Put

```text
r=|U|,
q=prod_(p in U)p,
kappa(q)=prod_(p|q)(p-2).
```

For the density and occupancy Boolean blocks

```text
R_U=tensor_(p in U) T_p tensor tensor_(p notin U) A_p,
E_U=tensor_(p in U) Delta_p tensor tensor_(p notin U) A_p,
```

the actual upward cutoff jump at `q` is

```text
K_U=(-1)^r(E_U-R_U).                                      (CJ1)
```

Its inertia on the full `Q`-dimensional CRT space is

```text
In(K_U)=((q+kappa(q))/2,(q-kappa(q))/2,Q-q).              (CJ2)
```

Equivalently, modulo its ambient kernel,

```text
K_U congruent q^(-2) I_(kappa(q))
       direct_sum H^((q-kappa(q))/2),                      (CJ3)
```

where `H` is a hyperbolic plane.  In particular every nonempty cutoff crossing is indefinite,
so neither direction of Loewner monotonicity can hold for the joined cutoff family.

The sign in `(CJ1)` is load-bearing.  The raw curvature `C_U=R_U-E_U` instead has active inertia

```text
((q+(-1)^(r+1)kappa(q))/2,
 (q-(-1)^(r+1)kappa(q))/2,0).                              (CJ4)
```

For `U=empty`, `E_U=R_U` and the jump is zero; `(CJ2)` intentionally excludes this case.

## Explicit positive core

Let

```text
Z_p={v:<e_0,v>=<w_p,v>=0},
Z_U=tensor_(p in U)Z_p tensor tensor_(p notin U) R e_0.
```

Then `dim Z_p=p-2`, `T_p|Z_p=0`, and `Delta_p|Z_p=-p^(-2)I`.  Hence `Z_U` is reducing and

```text
dim Z_U=kappa(q),
K_U|Z_U=q^(-2)I.                                           (CJ5)
```

For every `h` coprime to `q`, a local difference basis may be chosen with labels avoiding the two
roots `0` and `-h`.  Tensoring the local bases identifies the positive core with

```text
{a mod q : gcd(a(a+h),q)=1},                               (CJ6)
```

whose cardinality is `kappa(q)`.  Thus the index surplus is carried by an explicit root-avoidance
subspace, not merely by a numerical coincidence.

The coprimality condition in `(CJ6)` is essential.  If a prime divides `h`, its local survival
factor is `p-1`, not `p-2`.

## Proof

Work first on the active `q`-space.  With `U_p=[e_0,w_p]` and `J_0=diag(1,-1)`,

```text
T_p=U_p J_0 U_p^T,
R=U J U^T,
U=tensor U_p,
J=tensor J_0.                                               (CJ7)
```

Since `E=tensor Delta_p` is invertible, set

```text
G_p=U_p^T Delta_p^(-1) U_p
   =1/(2p-1) [p^2,       -p(p-1);
              -p(p-1),  -p(p-1)],
G=tensor G_p.                                                (CJ8)
```

The binary form `J-G` is balanced.  Indeed

```text
L_p=1/sqrt(4(p-1)^2-1) [-1,       2(p-1);
                        -2(p-1),  1]
```

satisfies

```text
L_p^T J_0 L_p=-J_0,
L_p^T G_p L_p=-G_p.                                        (CJ9)
```

Acting by `L_p` on one tensor factor therefore sends `J-G` by congruence to its negative, forcing
equal positive and negative indices.

It is also nonsingular.  The characteristic polynomial of `J_0 G_p` is

```text
z^2-pz+p^2(p-1)/(2p-1),                                   (CJ10)
```

whose two roots have modulus

```text
rho_p=p sqrt((p-1)/(2p-1))>1.                              (CJ11)
```

Every eigenvalue of `JG` is a tensor product of local roots, hence has modulus greater than one.
Thus `1` is not an eigenvalue and `J-G=J(I-JG)` is invertible.  Therefore

```text
In(J-G)=(2^(r-1),2^(r-1),0).                               (CJ12)
```

Apply Haynsworth inertia additivity to

```text
M=[-E,   U;
   U^T, -J].                                                (CJ13)
```

Taking the two Schur complements gives

```text
In(-J)+In(R-E)=In(-E)+In(-(J-G)).                           (CJ14)
```

The balanced binary terms cancel, so `In(R-E)=In(-E)`.  Each `Delta_p` has inertia `(1,p-1,0)`;
therefore

```text
sig(E)=prod_(p|q)(2-p)=(-1)^r kappa(q).                    (CJ15)
```

Multiplication by the jump sign in `(CJ1)` gives `sig(K_U)=kappa(q)`.  Together with active
dimension `q`, this proves `(CJ2)`.  The exterior rank-one anchor factors add exactly `Q-q` null
directions.  Equation `(CJ5)` identifies the unpaired positive part, so the complement is the
balanced hyperbolic block in `(CJ3)`.

Finally,

```text
tr(T_p)=tr(Delta_p)=1/p.                                   (CJ16)
```

Every jump is traceless, and every joined cutoff has the invariant trace

```text
tr(J_D)=prod_(p in P)(1-1/p).                              (CJ17)
```

## Positive no-go consequence

The theorem closes the source-free monotonicity route sharply:

- every nonempty jump contains positive and negative directions;
- when `2|q`, its active block is exactly hyperbolic and has no positive surplus;
- for odd `q`, the relative surplus is only the classical survival density
  `kappa(q)/q=prod_(p|q)(1-2/p)`;
- the surplus lies in the transverse sector where `R_U` vanishes, not in the rough-prime carrier;
- the RH-bearing joined vector remains cutoff-invariant.

Thus the missing RH input is still a source-specific correlation in the balanced hyperbolic
complement.  Inertia alone supplies no power saving.

## Novelty verdict

The exact diagonal-deleted shear inertia and the reducing root-avoidance core are absent from the
current corpus.  However, `common-profile-boolean-anchor-curvature.md` already defines the same
operator, `ReducedFrequencyMobiusAliasCollapse.lean` already contains the two-root survival
product, and the proof uses standard finite-dimensional inertia technology.  The result is the
strongest positive survivor of the cutoff-monotonicity no-go, but it is classified as a
source-specific bridge rather than significant new RH knowledge.

## Gates

- [x] correct jump sign separated from raw curvature sign
- [x] active support and ambient nullity separated
- [x] empty crossing excluded
- [x] all-binary block proved balanced and nonsingular
- [x] exact inertia and trace laws proved on paper
- [x] explicit root-avoidance positive core identified
- [x] parent/corpus collision audited
- [ ] exact jump theorem formalized in Lean

## Log

- 2026-07-18 -- Replaced the failed source-free monotonicity conjecture by the exact jump inertia
  classification `(CJ2)` and the reducing CRT root-avoidance core `(CJ5)`--`(CJ6)`.
- 2026-07-18 -- Hostile audit corrected the parity sign for raw `R_U-E_U`, added the ambient
  nullity `Q-q`, excluded the empty crossing, and downgraded the result to a project-local bridge.
