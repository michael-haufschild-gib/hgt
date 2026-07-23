# Theta-cusp reflected correlation-angle concavity

- **ID:** `theta-cusp-reflected-correlation-angle-concavity`
- **Stage:** 1-in-progress
- **Type:** CONJECTURE
- **Date:** 2026-07-23
- **Scientific status:** `[CONJECTURE] [SOURCE-PURE] [NO COMPUTATION] [NOT RH] [NOVELTY UNVERIFIED]`
- **Parent:** `hedenmalm-center-mixed-double-positivity-law.md`
- **Statement:** For the completed Riemann--Jacobi theta source, every normalized reflected product
  has a concave correlation angle on the nonnegative displacement half-line.

## Goal

Let

```text
k(x)=thetaCuspFullSource(x)>0,
L(x)=log k(x),
c(x)=-L''(x)>0.
```

For each reflection center `u`, define

```text
P_u(t)=k(u+t)k(u-t),
p_u(t)=P_u(t)/P_u(0),
theta_u(t)=arccos(p_u(t)).
```

The exact conjecture is

```text
theta_u is concave on [0,infinity) for every real u.                    (A)
```

This is a source theorem, not a positive-definiteness assumption.  It would close the strongest
finite-order residue currently isolated in the corpus: global order-three positive
semidefiniteness of Hedenmalm's actual center-mixed theta density.  It does not assert order four,
all finite orders, Fourier-current positivity, or RH.

## Gates

- [x] 0 → 1 in-progress: source-pure statement, exact attack, and parent-theory audit
- [ ] 1 → 2 fully-proven: complete paper proof, `[PROVED HERE]`, no open dependency
- [ ] 2 → 3 formalized: exact source theorem and unconditional order-three consumer, narrow build,
  axiom audit, generated index, and lint green
- [ ] 3 → 4 publication-ready: standalone theorem, proof, Lean certificate, and external priority
  review

## Exact nonlocal producer

Put

```text
S_u(t)=-log p_u(t)=2L(u)-L(u+t)-L(u-t),
q_u(t)=S_u'(t)=integral_(u-t)^(u+t) c(v) dv.
```

Then

```text
q_u'(t)=c(u-t)+c(u+t),
q_u''(t)=c'(u+t)-c'(u-t).
```

A sufficient source inequality for `(A)` is the reflected curvature contraction

```text
q_u''(t) <= 2 q_u(t) q_u'(t)                  for u in R, t>=0.          (RC)
```

Equivalently,

```text
t |-> p_u(t)^2 q_u'(t) is nonincreasing,                              (RC')
```

or, without logarithmic notation,

```text
P_u'(t)^2-P_u(t)P_u''(t)
  <= P_u(0)(-P_u''(0)).                                                (RC'')
```

Thus `(RC)` says that the strict log-concavity numerator of a reflected theta product is largest
at its reflection center.  This is the exact missing source sign; no matrix positivity appears in
its statement.

## Why the producer closes the order-three shell

Because `p_u=exp(-S_u)`,

```text
theta_u''(t)
 =p_u(t)/(1-p_u(t)^2)^(3/2)
    *((1-p_u(t)^2)q_u'(t)-q_u(t)^2).                                  (1)
```

Define

```text
H_u(t)=q_u(t)^2-(1-exp(-2S_u(t)))q_u'(t).
```

The initial value is `H_u(0)=0`, and direct differentiation gives the factorization

```text
H_u'(t)
 =(1-exp(-2S_u(t)))*(2q_u(t)q_u'(t)-q_u''(t)).                         (2)
```

Hence `(RC)` implies `H_u>=0`, and `(1)` gives `(A)`.  Also `theta_u(0)=0` and
`theta_u>=0`.  Concavity therefore implies subadditivity:

```text
theta_u(x+y) <= theta_u(x)+theta_u(y),          x,y>=0.                 (3)
```

The Castano--Paksoy--Zhang `3 x 3` correlation-angle criterion turns `(3)` into positive
semidefiniteness of

```text
[P_u(t_i-t_j)]_(t_0,t_1,t_2)=(0,x,x+y).
```

Finally,

```text
M_a(t)=integral_(0,infinity)
  r*sinh(a*r)*P_(r/2)(t) dr.
```

For `0<a<1/2`, this is a positive integrable mixture.  Integrating the nonnegative quadratic form
of each reflected `3 x 3` matrix proves positive semidefiniteness of every corresponding
center-mixed matrix.  The existing exact determinant criterion then discharges
`ThetaCuspCenterMixedNearCenterThreePointWall`, including its bounded noncoalesced shell.

## Internal frontier

- `[CORPUS]` `strictConcaveOn_thetaCuspLogSource` proves `c>0`.
- `[CORPUS]` `thetaCuspLogSource_fourthTuran_gt_one_hundred_sixty` proves

  ```text
  L''''(u)+4L''(u)^2>160,
  ```

  equivalently `c''(u)<4c(u)^2`.
- `[CORPUS]` that fourth-Turán law already proves the reflected fourth Hankel sign, the
  center-mixed fourth Hankel sign, the nested coalesced cusp, every fixed aspect-ratio ray, and one
  uniform coalesced square.
- `[CORPUS]` center curvature plus two-jet tail decay proves the cofinal order-three chamber and
  reduces the global order-three problem to one bounded two-gap shell.
- `[CORPUS]` every pairwise principal minor is strictly positive, so any remaining failure is a
  genuinely ternary determinant failure.
- `[CORPUS]` generic even positive strict log-concavity is insufficient: an explicit symbolic
  Schwartz counterfamily has off-axis transform zeros.  The present conjecture uses a nonlocal
  reflected-curvature law specific to the completed theta source.

The infinitesimal boundary of `(RC)` is exactly the proved fourth-Turán theorem.  Indeed, at
`t=0`, both sides of `(RC)` vanish, and their first derivatives give

```text
2c''(u) <= 8c(u)^2,
```

namely `c''(u)<=4c(u)^2`.  Thus `(RC)` is a genuine nonlocal continuation of existing source
knowledge rather than a renamed matrix wall.

## External parent boundary

Castano--Paksoy--Zhang, *Angles, triangle inequalities, correlation matrices and metric-preserving
and subadditive functions*, Linear Algebra Appl. 2014, arXiv:1407.2800, supplies the classical
`3 x 3` correlation-angle criterion used after `(A)`.  Schoenberg--Bochner theory supplies the
all-packet positive-definite parent, but that stronger endpoint is RH-bearing here.

Hedenmalm, *Spectral interpretation of Riemann zeta zeros*, arXiv:2606.17494, supplies the
theta-source spectral route but does not state `(A)` or `(RC)`.  The audited theta-kernel
log-concavity work stops at order two.  Recent finite-order Pólya-frequency and Toeplitz-minor
results concern coefficient or sum kernels, not this reflected translation product.

Targeted searches found no source theorem asserting correlation-angle concavity, reflected
log-curvature contraction, or global order-three positivity for Hedenmalm's center-mixed density.
Priority remains `[NOVELTY UNVERIFIED]`.

## Hostile attack

1. **Local obstruction survives.**  The Taylor obstruction to `(RC)` is exactly
   `c''<=4c^2`; the corpus proves it with a strict margin greater than `160`.  Equivalently,
   `theta_u(t)` has a strictly negative cubic correction after its positive linear term.
2. **Cofinal obstruction survives.**  In the theta tail, `c` is first-atom dominated and grows on
   the `exp(2|x|)` scale.  Consequently `q_u` grows while `p_u` collapses, which has the correct
   orientation for `(1)` and `(RC)`.  A proof still needs exact symbolic bounds, not an asymptotic
   assertion.
3. **Fixed-order shape theory does not prove it.**  The pointwise inequality
   `c''<4c^2` alone does not integrate automatically to `(RC)`; the missing comparison is

   ```text
   2*integral_(u-t)^(u+t) c(v)^2 dv
     <= (integral_(u-t)^(u+t) c(v)dv)*(c(u-t)+c(u+t)),                 (4)
   ```

   or a theta-specific replacement strong enough to control the same remainder.
4. **First-atom comparison has a seam.**  On a single positive half-line, the explicit first atom
   gives a rational-exponential candidate proof of `(RC)`.  When `[u-t,u+t]` crosses zero, the
   standalone reflected first atom has a cusp at the modular seam.  The completed theta source is
   smooth only after the modularly paired tail is retained.  Dropping that tail would repeat the
   already classified wrong-sign first-atom error.
5. **No RH leakage.**  The conclusion is only order three.  It neither gives the Fourier-current
   sign nor a Gram orbit for arbitrary node sets.

**Current verdict:** `SURVIVES PRELIMINARY ATTACK`.

## Analytic attack plan

Work with the already formalized first-atom decomposition on the nonnegative half-line,

```text
k=phi*(1+rho),
c=c_1-(log(1+rho))'',
c_1=4A+6A/(A-3/2)^2,       A=pi*exp(2x).
```

Split `(u,t)` into two exact chambers.

1. **Same-sign chamber `0<=u-t`.**  Prove `(RC)` for `c_1` by clearing the positive rational
   denominators in `A_-`, `A_+`.  Bound the perturbation by the derivative-ratio estimates already
   used in `ThetaCuspFullReflectionFourthTuran`; retain an explicit factor of `t` so the strict
   fourth-Turán margin closes the coalesced boundary uniformly.
2. **Seam-crossing chamber `u-t<0<u+t`.**  Use evenness to split the curvature integral at zero.
   Pair the two modular half-line atom expansions before estimation.  The target is a smooth
   paired remainder estimate with the same vanishing factor as the first-atom margin.
3. **Consumer.**  After `(RC)` is proved, derive `(1)`--`(3)`, integrate the resulting finite
   quadratic forms against `r*sinh(a*r)dr`, and connect the theorem directly to
   `ThetaCuspCenterMixedNearCenterThreePointWall`.

No Lean edit is permitted until both source chambers and the finite-mixture transfer have a
dependency-complete paper proof.

## Log

- 2026-07-23 — created directly in Stage 1 after internal-corpus and primary-literature audits.
  The compact order-three shell was selected as strongest non-RH-equivalent residue.  Correlation
  angle concavity was reduced to the source-only reflected curvature contraction `(RC)`; its
  infinitesimal law was identified exactly with the already proved strict fourth-Turán theorem.
  Hostile attack exposed the modular seam as the first unresolved source obligation.
