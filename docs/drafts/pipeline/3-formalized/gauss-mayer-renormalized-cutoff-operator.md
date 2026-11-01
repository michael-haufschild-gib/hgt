# Gauss–Mayer cutoffs: rank-one divergence and operator renormalization

- **Stage:** 3-formalized
- **Type:** Theorem
- **Parent:** [three approaches, A](../1-in-progress/argon-three-orthogonal-rh-approaches.md).

Let `D={z:|z−1|≤3/2}` and let `A(D)` be its Banach disc algebra, with supremum norm.
Write `w=2s` and use principal complex powers. Define

`L_{w,N}f(z)=Σ_{n=1}^N (n+z)^(−w)f(1/(n+z))`, `Pf(z)=f(0)`.

For every `Re w>0`, `w≠1`, a bounded operator `L_w^reg` satisfies, for `N≥1`,

`‖L_{w,N}−N^(1−w)/(1−w) P−L_w^reg‖ ≤ (|w|+B(w))/Re w · N^(−Re w)`,

where `M(w)=2^(Re w) exp(π|Im w|)` and
`B(w)=8M(w)+(5/2)|w|M(w+1)`.
For `Re w>1`, it agrees with the absolutely convergent ordinary branch sum.

For `0<Re w<1`,

`N^(w−1)L_{w,N} → P/(1−w)`,

`‖L_{w,N}‖/N^(1−Re w) → 1/|1−w|`, and `‖L_{w,N}‖ → ∞`.

Moreover, `L_{w,N}−N^(1−w)Q` converges in operator norm for some limit iff
`Q=P/(1−w)`. This classifies the leading subtraction among all bounded operators,
not just rank-one candidates.

Every nontrivial zeta zero `ρ` has `0<Re ρ<1`. Consequently the raw cutoffs at
Mayer parameter `s=ρ/2` diverge, including at critical zeros. This rules out
uncorrected branch truncations at those targets. It does not rule out Padé
approximants, the continued Mayer operator, or source-specific resonance exclusion.

## Proof

For `n≥1` and `z∈D`, `Re(n+z)≥n/2>0`, and
`|1−(n+z)|²≤|n+z|²`. Thus `1/(n+z)` lies in the smaller closed disc
`|u−1|≤1`, and its norm is at most `2/n`. Cauchy's estimate on radius `1/4`
within `D` gives `|f′|≤4‖f‖` on that smaller disc. Convexity then gives
`|f(u)−f(0)|≤4‖f‖|u|`.

The principal-power formula gives `|(n+z)^(−w)|≤M(w)n^(−Re w)`.
Differentiating the weight and integrating along the segment from `0` to `z`
gives `|(n+z)^(−w)−n^(−w)|≤(5/2)|w|M(w+1)n^(−Re w−1)`.
Splitting the branch remainder into

`(n+z)^(−w)[f(1/(n+z))−f(0)] + [(n+z)^(−w)−n^(−w)]f(0)`

bounds its operator norm by `B(w)n^(−Re w−1)`. Hence

`L_w^reg = ζ(w)P + Σ_{n≥1}(L_{w,n}−L_{w,n−1}−n^(−w)P)`

is well defined in the complete operator space. The integral-test tail is
at most `B(w)N^(−Re w)/Re w`. The corpus's exact zeta truncation identity
bounds the remaining scalar error by `|w|N^(−Re w)/Re w`, proving the estimate.

When `Re w<1`, the scalar `N^(w−1)` tends to zero. Multiplication of the
corrected convergence by this scalar yields the rank-one limit; `‖P‖=1`
gives the sharp norm asymptotic and divergence. Normalizing any other
convergent subtraction forces the same coefficient. When `Re w>1`, the
counterterm tends to zero and the ordinary branch sum converges absolutely.

## Lean certificate

Module: `RenormalizedIntersectionTheory/GaussMayerCutoffRenormalization.lean`.
Namespace: `GaloisForLFunctions.RenormalizedIntersectionTheory.MayerCutoff`.

- `cutoff_apply`: actual weighted inverse-branch formula on the disc algebra.
- `norm_corrected_cutoff_le`: explicit operator tail estimate.
- `regularized_eq_tsum_branch`: agreement in the original half-plane.
- `tendsto_scaled_cutoff`, `tendsto_cutoff_norm_ratio`, `tendsto_cutoff_norm_atTop`.
- `corrected_cutoff_converges_iff`: unique leading correction.
- `tendsto_nontrivialZero_cutoff_norm_atTop`: actual zeta specialization.

The final direct `lake --old env lean` check passed. All six public theorem
audits report only `propext`, `Classical.choice`, and `Quot.sound`. The module
is imported by its umbrella; no umbrella build was run.

## Scope and remaining mathematics

The local corpus already contained the scalar finite-part identity and tail bound.
The new bridge constructs the actual Banach disc-algebra operators and proves
operator-norm correction, exact divergence, and uniqueness. No literature-novelty
claim is made. [Order-zero nuclearity and geometric finite-rank approximation](gauss-mayer-renormalized-nuclear-expansion.md) are also Lean-certified. Fredholm
determinant comparison and exclusion of off-critical resonances remain separate
obligations.
