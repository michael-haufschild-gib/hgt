# HB source-FE general-kernel Peierls classification

- **ID:** HC52
- **Stage:** 3-formalized
- **Type:** THEOREM / CLASSIFICATION / RH FRONTIER
- **Source:** HC51 packetwise diagonal classification; literal BM source FE cocycle; arbitrary
  cross-fibre Peierls-kernel loophole
- **Statement:** Classify every complex-bilinear kernel form on finite Xi packets under literal
  source FE transport, construct unconditional transported kernels, and prove that no
  reflection-real kernel with nonzero physical diagonal can evade the RH obstruction.

## Corpus-led gap

HC51 proves the exact Ward equation only for diagonal weights. It leaves open whether arbitrary
mixed-copy terms can cancel the diagonal source cocycle defect. This is the largest remaining
algebraic loophole before the literal augmented Einstein--Teukolsky producer: a physical Peierls
form can contain continuum, direct, corner, or cross-QNM terms, so diagonal classification alone
does not control its complete finite-packet kernel.

For a kernel `K : XiZeroCopy -> XiZeroCopy -> C`, define

```text
B_K(x,y) = sum_q sum_r K(q,r) x(q) y(r).
```

Let `R` be Xi reflection and `kappa` the HC50 literal-source anti-linear FE cocycle. HC51 proves
the packet transport

```text
(T x)(R q) = kappa(q) conj(x(q)),
T^2 = 1.
```

## Theorem HC52-KERNEL

Full packet covariance

```text
B_K(Tx,Ty) = conj(B_K(x,y))                    for every finite x,y
```

holds exactly when every ordered pair satisfies

```text
K(Rq,Rr) kappa(q) kappa(r) = conj(K(q,r)).     (KW)
```

Define source-kernel conjugation

```text
(C K)(q,r) = conj(K(Rq,Rr) kappa(q) kappa(r)).
```

Then `C^2 = 1`, `(KW) <-> C K = K`, and `K + C K` is an unconditional Ward kernel. This is the
positive transported survivor: mixed-copy covariant forms exist without RH, but their kernel is
transported by the literal source cocycle rather than fixed by physical reflection.

## Fixed-form rigidity theorem

Call `K` reflection-real when

```text
K(Rq,Rr) = conj(K(q,r)).
```

If `K(q,q) != 0`, simultaneous reflection-reality and `(KW)` force

```text
kappa(q)^2 = 1,
```

hence `Re(q)=1/2` by HC50. Consequently, for every reflection-real kernel with nonzero diagonal
on every Xi copy,

```text
(forall x y, B_K(Tx,Ty)=conj(B_K(x,y))) <-> RH.
```

This closes the complete arbitrary cross-fibre loophole: off-diagonal terms may change the
transported form, but cannot cancel a fixed nonzero diagonal defect because basis-pair testing
isolates every kernel coefficient.

## Dependency-closed proof

1. Finite double-sum kernel form is bilinear in both packet variables.
2. Necessity follows by testing independent basis packets `single q 1`, `single r 1`.
3. Sufficiency follows by nested finite-support induction.
4. Source-kernel conjugation is an anti-linear involution from
   `kappa(Rq) conj(kappa(q)) = 1`.
5. Ward kernels are exactly fixed points and exactly the image of Reynolds symmetrization; for a
   fixed kernel `K`, choose preimage `K/2`.
6. Intersecting Ward fixed points with reflection-real kernels cancels a nonzero diagonal coefficient
   and invoke `hbXiPeierlsUnitSourceFECocycle_sq_eq_one_iff`.
7. This gives exact universal RH equivalence for every reflection-real everywhere-nonzero diagonal
   kernel.

Formal module:

`GaloisForLFunctions.RHTower.ThetaCuspHawkingBMSourceFEKernelPeierlsClassification`

Principal declarations:

- `forall_hbXiPeierlsKernelForm_packetTransport_iff_kernelWard`
- `hbXiPeierlsUnitSourceFEKernelConjugation_involutive`
- `kernelWard_iff_kernelConjugation_eq`
- `kernelWard_iff_exists_kernelSymmetrization`
- `kernel_diagonal_eq_zero_of_kernelWard_of_reflectionReal_of_tilt`
- `forall_hbXiPeierlsKernelForm_packetTransport_iff_rh_of_reflectionReal`

## Hostile checks

- No positivity, completeness, continuum truncation, or QNM basis premise may enter.
- Kernel is fully arbitrary and not assumed diagonal, symmetric, Hermitian, local, or finite-rank.
- Necessity must use independent basis pairs, not compare only diagonal values.
- Symmetrized transported kernels must not be mislabeled fixed physical kernels.
- RH may occur only in the final fixed-form identification, never in transport construction.
- All Lean theorems must be closed and axiom-audited; no choice of a hypothetical off-line zero.

## Novelty boundary as of 2026-08-28

Targeted corpus research located HC51's diagonal theorem but no arbitrary bivariate-kernel
classification. Targeted primary-literature search located the conserved complex-bilinear
Teukolsky/QNM form of Green--Hollands--Sberna--Toomani--Zimmerman (arXiv:2210.15935), but no
Xi-source cocycle, finite-packet kernel fixed-point classification, or RH rigidity theorem.
Generic real-structure/involution linear algebra is classical; claimed new content is the exact
literal-BM-source specialization and its arbitrary-kernel RH obstruction. Search is bounded, not
an exhaustive priority proof.

## Gates

- [x] 0 -> 1 in-progress: corpus gap, exact conjecture, hostile checks, bounded literature audit
- [x] 1 -> 2 fully-proven: dependency-closed paper proof and failed-conjecture audit
- [x] 2 -> 3 formalized: unconditional Lean module, targeted build, axiom/lint audit, umbrella wire
- [ ] 3 -> 4 publication-ready: independent priority audit and standalone exposition

## Log

- 2026-08-28 — Opened after HC51 closed every diagonal-weight loophole but left arbitrary
  cross-fibre kernels untreated.
- 2026-08-28 — Proved full ordered-pair Ward classification, source-kernel involution, exact
  symmetrization range, tilted-diagonal extinction, and arbitrary-kernel RH rigidity in Lean.
  Direct elaboration and target-only build passed. All 15 public theorem axiom audits report only
  `propext`, `Classical.choice`, and `Quot.sound`. Formal lint reports no HC52 issue; repository
  gate remains red only on unrelated unreachable modules.
