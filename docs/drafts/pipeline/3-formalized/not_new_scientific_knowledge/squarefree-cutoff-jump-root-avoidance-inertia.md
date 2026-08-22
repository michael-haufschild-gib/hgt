# Squarefree cutoff jumps have a root-avoidance signature and a hyperbolic complement

- **ID:** `squarefree-cutoff-jump-root-avoidance-inertia`
- **Stage:** 3-formalized / not new scientific knowledge
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
- [x] exact jump theorem formalized in Lean

## Log

- 2026-07-18 -- Replaced the failed source-free monotonicity conjecture by the exact jump inertia
  classification `(CJ2)` and the reducing CRT root-avoidance core `(CJ5)`--`(CJ6)`.
- 2026-07-18 -- Hostile audit corrected the parity sign for raw `R_U-E_U`, added the ambient
  nullity `Q-q`, excluded the empty crossing, and downgraded the result to a project-local bridge.

## Lean formalization

The theorem is formalized for an arbitrary nonempty finite family of local scales
`P_i = m_i + 2` (so `q = ∏ P_i`, `κ = ∏ m_i`); specializing `P_i` to the primes of `U` is the
arithmetic reading.  Every declaration is unconditional and depends only on `propext`,
`Classical.choice`, `Quot.sound`.

### Reusable inertia infrastructure (new, and absent from mathlib)

| Item | Lean declaration | Module |
|---|---|---|
| block-diagonal additivity of the inertia | `posIndex_fromBlocks_zero`, `negIndex_fromBlocks_zero`, `nullIndex_fromBlocks_zero` | `HTGeometry.HaynsworthInertia` |
| every Hermitian matrix is congruent to its eigenvalue diagonal | `exists_congr_diagonal` | `HTGeometry.HaynsworthInertia` |
| the Schur congruence `Sᴴ diag(A, C − Bᴴ A⁻¹ B) S = [[A,B],[Bᴴ,C]]` | `fromBlocks_schur_congr` | `HTGeometry.HaynsworthInertia` |
| **Haynsworth inertia additivity** | `haynsworth_posIndex`, `haynsworth_negIndex`, `haynsworth_nullIndex` | `HTGeometry.HaynsworthInertia` |
| rectangular congruence of the Hermitian form; isometric congruence preserves the inertia | `hermQuad_rect_conjugate`, `posIndex_isometric_congr`, `negIndex_isometric_congr` | `HTGeometry.IsometricCongruenceInertia` |
| positivity toolkit (`c·1 + AᴴA` is positive definite; `hermQuad` under vector scaling) | `hermQuad_add`, `hermQuad_one`, `hermQuad_one_pos`, `isPosDefOn_top_smul_one_add_gram`, `hermQuad_smul_vec` | `HTGeometry.IsometricCongruenceInertia` |
| positive rescaling, reindexing and block swap preserve the inertia; full positive index ⟹ positive definite; units are nonsingular | `posIndex_smul_pos`, `posIndex_submatrix_equiv`, `posIndex_swapBlocks`, `negIndex_swapBlocks`, `nullIndex_swapBlocks`, `isPosDefOn_top_of_posIndex_eq_card`, `nullIndex_eq_zero_of_isUnit`, `nullIndex_neg` | `HTGeometry.InertiaScalingSwap` |
| iterated Kronecker products: algebra, inertia, trace, action on tensor vectors | `tensorFamily`, `tensorFamily_mul`, `tensorFamily_conjTranspose`, `tensorFamily_diagonal`, `tensorFamily_smul`, `tensorFamily_inv`, `isUnit_tensorFamily`, `isHermitian_tensorFamily`, `posIndex_tensorFamily`, `negIndex_tensorFamily`, `trace_tensorFamily`, `tensorVec`, `tensorVec_smul`, `tensorFamily_mulVec` | `HTGeometry.TensorFamilyInertia` |
| the signed count `#{x : ∏ μ > 0} − #{x : ∏ μ < 0} = ∏_i (#{μ_i > 0} − #{μ_i < 0})` | `sum_prod_eq_prod_sum`, `card_pos_sub_card_neg_tensor` | `HTGeometry.TensorFamilyInertia` |

### The local blocks

| Paper item | Lean declaration | Module |
|---|---|---|
| the anchor `A = e eᴴ`, the occupancy `Δ = 2P⁻¹ e eᴴ − P⁻² 1`, the frame `U = [e, w]`, `J₀`, and the density `T = U J₀ Uᴴ` | `localAnchorBlock`, `localOccupancyBlock`, `localFrame`, `binaryJ`, `localDensityBlock`, `localColumn` | `RHTower.SquarefreeCutoffLocalBlocks` |
| identification with the parent card's arithmetic shear kernel `p·1_{i=o} + p·1_{j=o} − 1` | `localDensityBlock_apply`, `localDensityBlock_eq_smul_shearKernel` | `RHTower.SquarefreeCutoffLocalBlocks`, `RHTower.SquarefreeShearKernelSignedTensor` |
| `(CJ8)` the exact local Gram `G_p = (2P−1)⁻¹ [[P², −P(P−1)], [−P(P−1), −P(P−1)]]` | `frameGram_eq`, `inv_localOccupancyBlock`, `localGram_eq`, `localGramRaw`, `localGram_eq_smul` | `RHTower.SquarefreeCutoffLocalBlocks` |
| `(CJ9)` the balance `Lᴴ J₀ L = −f J₀`, `Lᴴ G L = −f G` with `f = 4(P−1)² − 1 > 0` | `localBalance`, `localBalanceFactor`, `localBalanceFactor_pos`, `isUnit_localBalance`, `localBalance_binaryJ`, `localBalance_gramRaw` | `RHTower.SquarefreeCutoffLocalBlocks` |
| `(CJ10)`,`(CJ11)` the pencil `M̃ = J₀ G̃`, its rotation part `Ñ` with `Ñ² = −ω̃²`, the invariant metric `P₀ = ω̃² 1 + ÑᴴÑ` and `M̃ᴴ P₀ M̃ = d̃ P₀` with `d̃ = P²(2P−1)(P−1) > 2P−1` | `localPencilRaw`, `localRotationRaw`, `localRotationRaw_sq`, `localMetric`, `isPosDefOn_localMetric`, `posIndex_localMetric`, `localPencilRaw_metric`, `localMetricScalar`, `two_realScale_sub_one_lt_metricScalar` | `RHTower.SquarefreeCutoffLocalBlocks` |
| `(CJ5)` local root avoidance: `T|Z = 0`, `Δ|Z = −P⁻²` | `localDensityBlock_mulVec_eq_zero`, `localOccupancyBlock_mulVec` | `RHTower.SquarefreeCutoffLocalBlocks` |
| `(CJ16)` `tr T = tr Δ = P⁻¹` | `trace_localOccupancyBlock`, `trace_localDensityBlock` | `RHTower.SquarefreeCutoffLocalBlocks` |

### The global jump

| Paper item | Lean declaration | Module |
|---|---|---|
| `E = ⊗ Δ_i`, `R = ⊗ T_i`, `V = ⊗ U_i`, `J = ⊗ J₀`, `G = ⊗ G_i` | `crossingOccupancy`, `crossingDensity`, `crossingFrame`, `crossingJ`, `crossingGram` | `RHTower.SquarefreeCutoffJumpInertia` |
| `(CJ7)` `R = V J Vᴴ`; `G = Vᴴ E⁻¹ V` | `crossingDensity_eq`, `crossingGram_eq` | `RHTower.SquarefreeCutoffJumpInertia` |
| `(CJ12)` the balance of `J` and of `J − G` | `tensorSingleFactor`, `tensorSingleFactor_congr`, `posIndex_crossingJ_eq_negIndex`, `posIndex_crossingJ_sub_gram_eq_negIndex` | `RHTower.SquarefreeCutoffJumpInertia` |
| `(CJ11)` nonsingularity of `J − G` through the invariant metric | `crossingPencil`, `crossingMetric`, `crossingMetric_posDef`, `crossingPencil_metric`, `crossingJ_mul_gram`, `crossingDenom_sq_lt_scalar`, `isUnit_crossingJ_sub_gram` | `RHTower.SquarefreeCutoffJumpInertia` |
| `(CJ13)`,`(CJ14)` Haynsworth at both corners of `[[−E, V], [Vᴴ, −J]]` | `schur_at_occupancy`, `schur_at_binary`, `haynsworth_pos_eq`, `haynsworth_neg_eq`, `haynsworth_null_eq` | `RHTower.SquarefreeCutoffJumpInertia` |
| `(CJ15)` `sig(E) = ∏ (2 − P_i) = ∏ (−m_i)` | `crossingOccupancy_eq_diagonal`, `crossingOccupancy_signature` | `RHTower.SquarefreeCutoffJumpInertia` |
| `(CJ1)` the jump `K = (−1)^r (E − R)` | `crossingJump`, `crossingJump_eq_of_even`, `crossingJump_eq_of_odd` | `RHTower.SquarefreeCutoffJumpInertia` |
| `(CJ2)` active dimension `q`, signature `κ`, and nonsingularity | `nullIndex_crossingJump`, `posIndex_add_negIndex_crossingJump`, `crossingJump_pos_add_neg`, `crossingJump_signature`, `crossingJump_signature_eq_kappa` | `RHTower.SquarefreeCutoffJumpInertia` |
| `(CJ2)` ambient nullity `Q − q` after rank-one anchor padding | `anchorPad`, `anchorPad_isometry`, `posIndex_anchorPad`, `negIndex_anchorPad`, `nullIndex_anchorPad_crossingJump` | `RHTower.SquarefreeCutoffJumpInertia` |
| `(CJ3)` `pos = neg + κ`, so the complement is `(q − κ)/2` hyperbolic planes | `posIndex_crossingJump_eq_negIndex_add`, `two_mul_negIndex_crossingJump` | `RHTower.SquarefreeCutoffJumpInertia` |
| `(CJ4)` the raw curvature has the opposite signature | `crossingCurvature_signature` | `RHTower.SquarefreeCutoffJumpInertia` |
| `(CJ5)` the jump is the positive scalar `q⁻²` on the root-avoidance core | `crossingJump_mulVec_core` | `RHTower.SquarefreeCutoffJumpInertia` |
| `(CJ16)` every jump is traceless | `trace_crossingOccupancy`, `trace_crossingDensity`, `trace_crossingJump` | `RHTower.SquarefreeCutoffJumpInertia` |

`(CJ6)` -- the identification of the `κ`-dimensional core with `{a mod q : gcd(a(a+h), q) = 1}` --
is the arithmetic reading of `(CJ5)`: the Lean statement gives the core as the tensor of the local
root-avoidance spaces and its dimension as `∏ m_i = ∏ (p − 2) = κ(q)`, which is exactly the
two-root CRT survival count already formalized in `ReducedFrequencyMobiusAliasCollapse.lean`.

