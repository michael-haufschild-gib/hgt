# Suzuki causal depth fusion is an exact Frostman transfer

- **ID:** `suzuki-causal-depth-frostman-transfer`
- **Stage:** 3 — formalized in Lean 4
- **Formalized companion:** `./suzuki-causal-depth-frostman-transfer-formalized.md`
- **Type:** THEOREM / SUZUKI--CCM SOURCE CONNECTOR / HEIGHT SEPARATION
- **Scientific status:** `[PROVED] [CANDIDATE NEW SCIENTIFIC KNOWLEDGE]`
  `[EXTERNAL NOVELTY UNVERIFIED] [NOT AN RH PROOF]`
- **Parents:**
  `suzuki-critical-aperture-quarter-shift-current.md`,
  `suzuki-critical-entry-wall-quarter-shift-green-law.md`,
  `suzuki-aperture-dressed-wall-light-completion.md`, and the corpus CCM transverse
  Frostman profile.
- **RH used:** no
- **Computation used:** no

## Frontier and competing conjectures

S62 proves that the aperture-dressed wall vector is in the all-prime Hilbert space, but its
diagonal energy is exactly height-flat.  The unresolved RH-bearing problem is to construct the
actual pre-split transfer which creates height dependence before the restricted-Weil/Robin/Gamma/
holonomy Ward trace is formed.

Four falsifiable possibilities were tested.

1. Squaring each valuation depth and then summing could create height dependence.  **False:** this
   is exactly the S62 height-flat law.
2. Summing the causal entry-wall depths before squaring could create height dependence.  **True:**
   the existing geometric depth recursion turns the diagonal into an exact Poisson profile.
3. One prime profile could select real height globally.  **False:** one prime clock is periodic.
4. Two distinct prime profiles could have a unique common maximum.  **True:** equality in both
   profiles recovers both prime phases, and the corpus incommensurate-clock theorem then recovers
   height exactly.

The survivor is `SUZUKI-CAUSAL-DEPTH-FROSTMAN-TRANSFER` below.  It is source-first: no Xi zero,
divisor, RH-equivalent positivity premise, fitted transfer matrix, or target interpolation enters.

## Exact source law

Fix `h,a>0` and a prime `p`.  Put

```text
d_p = xiMobiusContinuousApertureDiskNode((h/2)a,p),
r_p = exp(-(log p)/4) d_p^2,
z_p(t)=exp(i t log(p)/2),
A_p = suzukiCriticalEntryWallEndpointAmplitude(h,a,p,0).
```

The aperture disk law gives `0<d_p<1`; the Gamma quarter shift gives
`0<exp(-(log p)/4)<1`.  Hence

```text
0 < r_p < 1.                                                   (F1)
```

Let `psi_t(p,e)` be the actual dressed critical wall atom from S62 and fuse one causal
prime-power ray before taking a square:

```text
R_p(t) = sum_(e>=0) psi_t(p,e).                                (F2)
```

The existing depth recursion and entry-wall calibration say

```text
psi_t(p,0)=A_p z_p(t),
psi_t(p,e+1)=r_p z_p(t) psi_t(p,e).
```

Since `r_p<1`, the sum is unconditional and exact:

```text
R_p(t)=A_p z_p(t)/(1-r_p z_p(t)).                              (F3)
```

This is not an arbitrary resolvent.  By the causal Green law, its summands are precisely the
calibrated prime-power entry-wall third-jet forcings after removing their common `t^2` factor.

## Suzuki--CCM Frostman identity

For `theta_p(t)=t log(p)/2`, unit modulus of `z_p(t)` gives

```text
|R_p(t)|^2
 = A_p^2/(1-2 r_p cos(theta_p(t))+r_p^2).                      (F4)
```

At `t=0`, the denominator is `(1-r_p)^2`.  Therefore

```text
|R_p(t)|^2/|R_p(0)|^2
 = (1-r_p)^2/(1-2 r_p cos(theta_p(t))+r_p^2)
 = ccmFrostmanPoissonProfile(r_p^(-1),theta_p(t)).             (F5)
```

Equation `(F5)` is the new connector: Suzuki's actual causal valuation-depth resolvent and the
CCM prime-transverse model have exactly the same normalized Poisson geometry, with the
source-selected CCM parameter `q_p=r_p^(-1)>1`.

Write this normalized diagonal as `P_p(t)`.  Existing exact CCM algebra now gives

```text
ccmFrostmanProfileFloor(r_p^(-1)) <= P_p(t) <= 1,              (F6)
P_p(t)=1  <->  cos(theta_p(t))=1
          <->  z_p(t)=z_p(0).                                 (F7)
```

The second equivalence in `(F7)` follows without a branch choice: for a unit phase,
`|1-z|^2=2-2 cos(theta)`.

## Two-prime faithful height separation

Let `p!=q` be primes and define

```text
P_(p,q)(t)=P_p(t)+P_q(t).                                     (F8)
```

By `(F6)`, `P_(p,q)(t)<=2`.  Equality forces both prime phases to equal their values at zero.
The corpus theorem `primeLogPhaseClockPair_injective`, based on irrationality of
`log(q)/log(p)`, applied at time `t/2`, gives

```text
P_(p,q)(t)=2  <->  t=0.                                      (F9)
```

Consequently

```text
D_(p,q)(t,u)=2-P_(p,q)(t-u)                                  (F10)
```

is an unconditional translation-invariant nonnegative height separator:

```text
D_(p,q)(t,u)>=0,
D_(p,q)(t,u)=0  <->  t=u.                                    (F11)
```

No claim that `sqrt(D)` satisfies the triangle inequality is made.

## What this advances and what remains open

This closes the immediate structural question left by S62: actual Suzuki source data already
contains a non-flat pre-square transfer.  Correct operation is **causal valuation fusion before
the Gram square**, and its height law is rigidly fixed rather than fitted.  Two primes remove the
periodic ambiguity and yield a faithful scalar height separator.

It does not prove RH.  Profile `(F5)` is a primewise diagonal response.  It neither identifies
Suzuki's concrete restricted-Weil/Robin/polar--Gamma/holonomy transfer nor proves a lower bound for
the rectangular Ward remainder.  Also `(F6)` shows that one fused prime channel retains a positive
Frostman floor; it cannot by itself implement the signed cross-prime cancellation required by the
Xi trace.

The sharpened open core is therefore:

> Prove that the concrete restricted-Weil rectangular carrier contains the causal depth-fused
> Frostman diagonal `(F5)` plus a source-derived cross-prime/archimedean correction, identify its
> FE-negative projection including Robin/Gamma/holonomy Schur tax, and prove the resulting
> rectangular Ward remainder uniformly lower bounded.

That statement is not positivity to avoid because it is RH-bearing.  It must be proved
unconditionally from the concrete source; this theorem supplies the first exact non-flat diagonal
term that such a proof must preserve.

## Collision and novelty audit

Internal search covered wall modulation, prime clocks, quarter-shift resolvents, coherent fusion,
Poisson profiles, and Frostman profiles.  Corpus contains all parent identities separately but no
Suzuki causal-depth/Frostman identification, no normalized energy law `(F5)`, and no two-prime
separator `(F11)`.

Targeted primary-source search checked Suzuki's 2026 screw-function paper and arXiv combinations of
Suzuki, quarter shift, depth resolvent, Poisson/Frostman profile, and prime clocks.  No matching
statement was found.  This is evidence only; external priority remains unverified.

## Gates

- [x] exact frontier stated from S62
- [x] coordinatewise-square and one-prime alternatives falsified
- [x] causal depth fusion derived from existing source recursion
- [x] exact Suzuki--CCM Frostman identity proved
- [x] two-prime unique-maximum and height-separation law proved
- [x] RH circularity audit passed
- [x] formalize in Lean and connect to `RiemannHypothesisSOTA2026`
- [ ] identify `(F5)` inside the concrete restricted-Weil rectangular trace
- [ ] prove cross-prime/archimedean Ward lower bound
- [ ] RH
