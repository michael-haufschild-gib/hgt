# Gamma conductor deletion and strict prime-depth faithfulness

- **ID:** `gamma-conductor-deletion-strict-prime-depth-faithfulness`
- **Stage:** 3 — formalized
- **Type:** UNIVERSAL GAMMA LAW / STRICT KERNEL THEOREM / SUZUKI SOURCE INTERFACE
- **Scientific status:** `[NEW IN CORPUS] [NO LITERATURE COLLISION FOUND] [EXTERNAL NOVELTY NOT YET CERTIFIED]`
- **RH used:** no
- **Computation used:** no

## Universal theorem

Let `mu_Gamma` be the normalized symmetric Gamma cyclic measure whose characteristic function is

```text
phi(t)=cosh(t)^(-1/2).
```

Center the Fourier modes, then orthogonally remove the centered second spectral moment.  The
resulting Schur kernel is

```text
K_Gamma(t,u)
 = phi(t-u)-phi(t)phi(u)-kappa(t)kappa(u)/(3/2),

kappa(t)=-(3/4)phi(t)tanh(t)^2.
```

If `J_n(t)` denotes the normalized real Gamma-Jacobi Fourier feature, then

```text
K_Gamma(t,u)
 = J_1(t)J_1(u) + sum_(n>=3) J_n(t)J_n(u).                 (1)
```

Thus centering deletes Jacobi degree zero and conductor projection deletes exactly degree two.
No other Gamma-Jacobi mode is lost.

For every finite packet of pairwise distinct positive frequencies `t_1,...,t_N`,

```text
sum_(i,j) c_i K_Gamma(t_i,t_j)c_j > 0                     (2)
```

for every nonzero real coefficient vector `c`.  In particular, the Schur kernel is strictly
positive definite, not merely positive entrywise.

Proof of strictness uses only the consecutive surviving tail `n=3,...,N+2`.  After extracting
positive diagonal factors, these features are the Vandermonde system

```text
tanh(t_i)^3, tanh(t_i)^4, ..., tanh(t_i)^(N+2).
```

## Suzuki source theorem

For a prime-depth coordinate `(p,e)`, define

```text
tau_(p,e) = (1/2) log(p^(e+1)),
w_(p,e)   = A_(p,0) r_p^e,
```

where `A_(p,0)>0` is the actual critical entry-wall endpoint amplitude and `0<r_p<1` is the actual
causal depth-fusion radius.  Unique factorization makes the complete frequency map
`(p,e) -> tau_(p,e)` injective.

The weighted projected Gamma kernel

```text
G((p,e),(q,f))
  = w_(p,e) K_Gamma(tau_(p,e),tau_(q,f)) w_(q,f)           (3)
```

is strictly positive definite on every finite packet of distinct prime-depth coordinates.  The
weight is not fitted: `w_(p,e)^2` is exactly the squared norm of the corresponding critical Suzuki
wall atom.

## What changed at the RH frontier

Previous corpus result proved only

```text
K_Gamma(t,u)>0
```

for one pair of positive frequencies.  Entrywise positivity does not prevent a finite arithmetic
packet from having a null direction.  Equations `(1)`–`(3)` remove that gap: centered conductor
projection is faithful on every finite causal prime-depth packet.

This closes the finite Gamma-projection gate in the coherent Suzuki weld.  It rules out one
possible failure mode: the common Gamma conductor payment cannot collapse a nonzero finite
arithmetic source direction.

It does **not** identify `(3)` with the concrete division-free Robin--Gamma rectangular trace.
Current right-to-left chain is

```text
compact gated wall source
  -> closed unbounded restricted-Weil source recovery                    [OPEN]
  -> coherent causal response
  -> centered Gamma conductor projection                                [FINITE FAITHFULNESS PROVED]
  -> concrete Robin--Gamma rectangular trace identity                    [OPEN]
  -> marked-halfgap and holonomy graph debts                             [OPEN]
  -> uniformly lower-bounded rectangular Ward residual                  [OPEN]
  -> RH.
```

## Collision audit

- `GammaConductorSchurResidual` proves entrywise strict positivity only.
- `GammaOddJacobiCapacity` gives an odd sine-covariance Mercer expansion, not the mean-and-quadratic
  conductor deletion law `(1)` and not finite-packet strictness `(2)`.
- `GammaConductorSchurCapacity` proves divergence of independently scalarized prime costs; it does
  not prove faithfulness of the coherent Schur kernel.
- `SuzukiCoherentCausalDepthFusion` proves all-prime coherent response existence and a faithful
  height cap, but does not pass that source through Gamma conductor projection.
- Repository-wide declaration and pipeline searches found no prior version of `(1)`, `(2)`, or
  source specialization `(3)`.
- Targeted searches of arXiv and primary journal indexes found classical hyperbolic-secant and
  Meixner--Pollaczek background, but no statement matching the two-coordinate deletion spectrum,
  strict positive definiteness on distinct positive frequencies, or the prime-depth
  specialization.  This is evidence against collision, not a complete external novelty proof.

## Internal verification

- `GammaConductorSchurStrictDefiniteness`
- `SuzukiCausalDepthGammaSchurCoherence`
- Direct file checks passed.
- Final lint, axiom, and cached module-build audit pending.
