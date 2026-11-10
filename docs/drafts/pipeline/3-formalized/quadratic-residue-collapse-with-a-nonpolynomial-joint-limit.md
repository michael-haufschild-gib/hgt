# Quadratic residue collapse with a nonpolynomial joint limit

- **ID:** B130-quadratic-boundary-scaling
- **Stage:** 3-formalized
- **Type:** THEOREM — formalized
- **Source:** [Logarithmic residue collapse](../3-formalized/liouville-boundary-residue-logarithmic-collapse.md).

## Theorem

For `v_p(z)=exp(-iπ exp(-z log p))`, the endpoint phases are Liouville.
For real `t>0`, prime deviations from one decay like `p^(-t)`.
Let `U` be the canonical interior pole regularization. Then, as `t→0⁺`,

`t^(-2) U(t,1+tw) → Q(w)` locally uniformly on `Re w>-1`, where

`Q(w)=ζ(2) exp(-Σ_{k≥1} ((-iπ)^k/k!) log(w+k))`.

In particular, the pole residue vanishes quadratically with nonzero
coefficient `Q(0)`. Nevertheless, no actual joint holomorphic endpoint
regularization exists: its quadratic Taylor term would make `Q` a
polynomial of degree at most two.

## Paper proof

Write `a_k=(-iπ)^k/k!`, `P(s)=Σ_p p^(-s)`, and
`D_u(s)=Σ_p[-log(1-u_p p^(-s))-u_p p^(-s)]`.
Here `D_+` and `D_-` denote constant phases `+1` and `-1`.
Let `Z(s)=(s-1)ζ(s)`, extended by `Z(1)=1`.

**Prime logarithm.** On a sufficiently small right half-disc at one,

`E(s):=P(s)+log(s-1)=log Z(s)-D_+(s)`.

Indeed, the Euler logarithm is `P+D_+`. Its exponential is `ζ`.
On the real interval to the right of one the logarithms are real, so
the displayed identity holds there; the analytic identity theorem
extends it to the connected half-disc. Consequently `E` has an
analytic germ at one and `E(1)=-D_+(1)`.

**Uniform estimate.** Fix compact `K⊂{Re w>-1}`. Choose `η>0,M≥1`
with `Re(w+1)≥η` and `|w|≤M` on `K`. For `0<t≤1`, `k≥1`,
`δ=t(w+k)` lies in a fixed closed sector strictly inside `Re δ>0`:
`|Im δ|/Re δ≤M/η`. When `Re δ<ε` for sufficiently small fixed `ε`,
`1+δ` lies in the analytic germ's disc, where `E` is bounded.
Otherwise `|P(1+δ)|≤P(1+ε)`, `ε≤|δ|≤k+M`, and `|arg δ|≤π/2`.
Thus, uniformly in `t,w,k`,

`|E(1+t(w+k))|≤C_K+k`.

The factorial weights make this majorant summable. For each fixed `k`,
`E(1+t(w+k))→-D_+(1)` uniformly on `K`.

**Joint scaling.** Taylor expansion of each prime phase and absolute
summation give, whenever `Re s+t>1`,

`Σ_p(v_p(t)-1)p^(-s)=Σ_{k≥1} a_k P(s+kt)`.

The absolute double sum is bounded by
`(exp π-1)P(Re s+t)`. Since `Σ_{k≥1}a_k=-2`, substitution
`s=1+tw` yields

`Σ_p(v_p(t)-1)p^(-s)=2 log t-Σ_{k≥1}a_k log(w+k)+Σ_{k≥1}a_k E(1+t(w+k))`.

The last sum converges locally uniformly to `2D_+(1)` by the preceding
majorant. For `t` sufficiently small, `Re(1+tw)≥3/4` on `K`.
The higher-power Euler summands satisfy the common summable bound
`2p^(-3/2)`; each converges uniformly on `K` to its phase `-1`
value at one. Therefore `D_v(t)(1+tw)→D_-(1)` and
`D_+(1+tw)→D_+(1)`, both locally uniformly.

The linear prime terms cancel in `D_-+D_+`; real logarithms give
`exp(D_-(1)+D_+(1))=ζ(2)`. Multiplying the exponential deformation
by `Z(1+tw)→1` proves exactly the asserted locally uniform limit `Q`.
In particular `U(t,1)/t²→Q(0)≠0`.

**Nonpolynomial limit.** The factorial logarithm series converges
normally on `Re w>-1`. Separating `k=1` gives

`Q(w)=exp(iπ log(w+1))R(w)`,

where `R(w)=ζ(2)exp(-Σ_{k≥2}a_k log(w+k))` is analytic and nonzero
on `|w+1|<1/2`. Along `w=-1+exp(-2n)` and
`w=-1+exp(-(2n+1))`, the two limits are respectively `R(-1)` and
`-R(-1)`. Thus `Q` has no continuous extension at `-1` and cannot
agree with any polynomial. If `U` extended jointly holomorphically
near `(0,1)`, finiteness of every scaled limit would annihilate its
Taylor terms of degrees zero and one, and its degree-two homogeneous
term evaluated at `(1,w)` would equal `Q(w)`, a contradiction.

**Moving branch.** Fix sufficiently small `t>0`, and put `s₀=1-t`.
Taylor's remainder gives
`|v_p(t)-1+iπp^(-t)|≤C p^(-2t)`, with an absolute constant `C`.
Its prime Dirichlet sum is analytic on `Re s>1-2t`; the higher-power
remainders are analytic on `Re s>1/2`. Hence near `s₀`, on its right,

`H(t,s)=iπ log(s-s₀)+B_t(s)`

with `B_t` analytic near `s₀`, using the prime-logarithm germ above.
Since `Z` is nonzero near one,

`U(t,s)=A_t(s)exp(iπ log(s-s₀))`, `A_t=Z exp(B_t)`,

and `A_t(s₀)≠0`. This also excludes a continuous extension at the
moving boundary point. A hypothetical joint endpoint regularization
agrees with this slice by analytic uniqueness on the connected
intersection of its spectral disc with `Re s>s₀`, giving the same
contradiction.

## Significance and formal status

Quadratic residue collapse matches the endpoint's zero order but does
not imply joint specialization. The exact scaling profile is
nonpolynomial; its first singularity is a moving branch with exponent
`iπ`. This explicit profile and branch factorization are the positive
survivors of the specialization obstruction. They identify spectral
information invisible to the residue order alone.

Lean modules under `ArithmeticWeightTheory/GaugeDeformations/`:

| Module | Main declarations |
|---|---|
| `ExponentialPrimePhase.lean` | `exponentialPhase_interior_poles`, `analyticOnNhd_exponentialPhasePrimeRemainder` |
| `PrimeLogarithmRenormalization.lean` | `exists_primeLogRegularPart_germ` |
| `MovingPhaseBranch.lean` | `exponentialPhase_moving_branch_factorization`, `exponentialPhase_moving_branch_unit`, `exponentialPhase_moving_branch_no_continuous_extension`, `exponentialPhase_no_joint_endpoint_regularization` |
| `QuadraticResidueScaling.lean` | `tendstoLocallyUniformlyOn_exponentialPhase_quadratic`, `tendsto_exponentialPhase_residue_quadratic`, `quadraticResidueScalingProfile_not_polynomial`, `exponentialPhase_quadratic_residue_coefficient_ne_zero` |

All listed statements are Lean checked. Their transitive dependency
audits contain only `propext`, `Classical.choice`, and `Quot.sound`.
All four final direct module audits passed without warnings.
No external novelty claim.
B130's arithmetic Stepanov bound remains open.

[Next conjecture: universal analytic smoothing obstruction](../2-fully-proven/universal-moving-branch-for-analytic-prime-smoothing.md).
