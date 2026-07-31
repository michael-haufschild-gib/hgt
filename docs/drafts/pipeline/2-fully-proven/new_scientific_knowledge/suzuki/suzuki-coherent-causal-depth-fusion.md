# Suzuki coherent causal-depth fusion creates an all-prime cross-prime Gram

- **ID:** `suzuki-coherent-causal-depth-fusion`
- **Stage:** 2 — fully proved on paper
- **Type:** THEOREM / GLOBAL SOURCE CARRIER / FAITHFUL HEIGHT SEPARATION
- **Scientific status:** `[PROVED] [CANDIDATE NEW SCIENTIFIC KNOWLEDGE]`
  `[EXTERNAL NOVELTY UNVERIFIED] [NOT AN RH PROOF]`
- **Parent:** `suzuki-causal-depth-frostman-transfer.md`
- **RH used:** no
- **Computation used:** no

## Theorem

Fix `h,a>0`, put `alpha=ha/2`, and for each prime `p` set

```text
d_p=p^(-alpha),
r_p=p^(-(1/4+2 alpha)),
z_p(t)=exp(i t log(p)/2),
A_p=(h sqrt(h))^(-1) sqrt(log(p)) p^(-1/4)
      (p+1)^(-1)(1-d_p)^2.
```

The already proved causal-depth law is

```text
R_p(t)=sum_(e>=0) psi_t(p,e)=A_p z_p(t)/(1-r_p z_p(t)).       (1)
```

Then:

1. `sum_p |R_p(t)|` converges uniformly in real `t`;
2. the coherent field `R(t)=sum_p R_p(t)` is therefore well defined before any Gram square;
3. `R(-t)=conjugate(R(t))`;
4. its energy has an absolutely convergent full double-prime expansion

   ```text
   |R(t)|^2=sum_(p,q) R_p(t) conjugate(R_q(t));              (2)
   ```

5. with `C=sum_p |R_p(0)|`,

   ```text
   C^2-|R(t-u)|^2 >= 0,
   C^2-|R(t-u)|^2 = 0  <->  t=u.                            (3)
   ```

## Proof

At depth zero, the critical Gamma factor has modulus

```text
sqrt(log(p) p^(-1/2))=sqrt(log(p))p^(-1/4),
```

while cubic innovation contributes

```text
(h sqrt(h))^(-1)(p+1)^(-1)(1-p^(-alpha))^2.
```

This gives the displayed `A_p`.  Since `0<d_p<1` and
`r_p<=2^(-1/4)<1`, reverse triangle inequality gives one constant `M_h` independent of `p,t` with

```text
|R_p(t)| <= M_h sqrt(log(p)) p^(-5/4).
```

For `x>=0`, `(sqrt(x)-1)^2>=0` gives `sqrt(x)<=(1+x)/2`.  Hence

```text
|R_p(t)| <= (M_h/2)(1+log(p))p^(-5/4).                      (4)
```

Both terms in `(4)` are absolutely summable because their Dirichlet exponent `5/4` is strictly
larger than one.  This proves uniform absolute convergence and permits rearrangement of the
double sum in `(2)`.  Reflection follows termwise from the real innovation and the existing wall
reflection law.

For each prime, the exact Frostman identity gives

```text
|R_p(t)|<=|R_p(0)|.                                         (5)
```

Triangle inequality and `(5)` imply `|R(t)|<=C`, proving nonnegativity in `(3)`.  If equality
holds, both inequalities are equalities.  The absolutely summable nonnegative deficits

```text
delta_p=|R_p(0)|-|R_p(t)|
```

therefore sum to zero, so every `delta_p` is zero.  In particular the Frostman profiles for primes
`2` and `3` both attain their caps.  The proved incommensurate two-prime clock theorem then forces
`t=0`.  The converse is immediate because all central rays are positive real.  Replacing `t` by
`t-u` proves `(3)`.

## Scientific advance

S63 supplied non-flat diagonal response separately on each prime ray.  This theorem proves the
actual source damping is strong enough to fuse distinct primes coherently before squaring.  The
off-diagonal terms `p!=q` in `(2)` are therefore a legal, cofinal, source-derived cross-prime
correction.  They are not fitted covariance and are not introduced after FE light splitting.

This resolves one explicit part of `SUZUKI-RESOLVENT-RECTANGULAR-LIGHT-INTERTWINER`: existence,
cofinal summability, FE compatibility, and faithful height observability of a concrete coherent
cross-prime carrier.

It does not identify `(2)` with Suzuki's actual rectangular Robin--Gamma--holonomy trace.  Nor does
it prove that the residual Ward defect is lower bounded.  Those are the remaining RH-bearing
claims.

## Collision and circularity audit

Internal search found the per-prime causal Frostman law, all-prime coordinatewise `ell^2` wall
field, abstract Gamma coherent-covariance necessity, and many Euler/Fock tensor products.  It found
no all-prime `ell^1` theorem for the causal fused rays, no coherent scalar sum `(2)`, and no faithful
global cap `(3)` for this source.  External priority is unverified.

Proof uses only positive-aperture source formulas, zeta-Dirichlet summability at exponent `5/4`,
triangle inequality, and prime-log incommensurability.  No Xi divisor or RH-equivalent sign enters.

## Gates

- [x] exact endpoint damping identified
- [x] all-prime `ell^1` majorant proved
- [x] cofinal double-prime Gram proved
- [x] FE reflection proved
- [x] faithful global cap proved
- [x] formalize and import into `RiemannHypothesisSOTA2026`
- [ ] identify Gamma-projected coherent Gram in actual rectangular trace
- [ ] prove Ward residual uniformly lower bounded
- [ ] RH
