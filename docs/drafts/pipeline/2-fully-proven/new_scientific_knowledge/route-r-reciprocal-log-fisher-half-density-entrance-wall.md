# Route R reciprocal-log Fisher half-density entrance wall

- **ID:** `route-r-reciprocal-log-fisher-half-density-entrance-wall`
- **Stage:** 2 — fully proved on paper
- **Type:** THEOREM / ONE-VECTOR DOMAIN SELECTOR / SOURCE-PURE PRODUCER INTERFACE
- **Scientific status:** `[PAPER-PROVED] [CORPUS-NEW] [NOVELTY UNVERIFIED] [NOT RH]`
- **Statement:** The inverse prime-log potential of the positive Euler--Fisher half-density is a
  genuine `ell^2` vector, lies exactly at the first prime-log form wall, and admits the physical
  fixed-orientation half-density transport precisely on the nonpositive centered-grade side.  Thus
  one explicit source vector, rather than a common Hilbert model for every grade, detects every
  right-half Xi fibre by failure of physical Cauchy landing.

## 1. Fixed pre-divisor vector

For an ordinary prime `p`, let

\[
 F_p=\frac{p}{(p+1)^2},\qquad L_p=\log p,
 \qquad v_p=\frac{\sqrt{F_p}}{L_p}.
\tag{1}
\]

Here `F_p` is the already constructed Euler activation Fisher density.  Its positive square root
is fixed by the source polarization, and `L_p^{-1}` is the Cartier potential for the prime-log
derivation.  Nothing in `(1)` depends on a divisor, a zero, or a choice of prime enumeration.

On `H=ell^2(P)` let `D e_p=L_p e_p`.  For real centered grade `t`, define the physical radial
transport of the fixed vector by

\[
 (V_t v)_p=p^{t/2}v_p.
\tag{2}
\]

If `s` is a complex spectral parameter and `t=2 Re(s)-1`, this is exactly the modulus of the
inverse physical half-density character:

\[
 \|p^{1/2-s}\|^{-1}=p^{\operatorname{Re}s-1/2}=p^{t/2}.
\tag{3}
\]

Thus `(2)` is not a fitted damping.  Its squared gain is the formalized Deninger mate gain
`p^t`.

## 2. Exact entrance-wall theorem

### Theorem 1 — maximal prime-log regularity

The fixed vector obeys

\[
 \boxed{v\in\operatorname{Dom}(D^\alpha)\ \text{for every }0\le\alpha<1,
 \qquad v\notin\operatorname{Dom}(D).}
\tag{4}
\]

#### Proof

For every prime `p>=2`,

\[
 \frac1{4p}\le F_p\le\frac1p.
\tag{5}
\]

The upper bound and the integral test give

\[
 \sum_p|v_p|^2
 =\sum_p\frac{F_p}{L_p^2}
 \le\sum_{n\ge2}\frac1{n(\log n)^2}<\infty.
\tag{6}
\]

More generally, for `0<=alpha<1`,

\[
 \|D^\alpha v\|^2
 =\sum_p\frac{F_p}{(\log p)^{2-2\alpha}}
 \le\sum_p\frac1{p(\log p)^{2-2\alpha}}<\infty.
\tag{7}
\]

Every last prime sum converges because `2-2 alpha>0`: the elementary Chebyshev bound
`pi(x)=O(x/log x)`, applied on dyadic prime blocks, bounds its `k`th block by a constant times
`k^(-(3-2 alpha))`.  On the other hand, `(5)` and Euler's divergence of the reciprocal-prime sum
give

\[
 \|Dv\|^2=\sum_pF_p\ge\frac14\sum_p\frac1p=\infty.
\tag{8}
\]

This proves `(4)`. `QED`

### Theorem 2 — one-sided physical entrance domain

For every real `t`,

\[
 \boxed{V_t v\in H\quad\Longleftrightarrow\quad t\le0.}
\tag{9}
\]

Consequently

\[
 \boxed{V_t v\in H\ \text{and}\ V_{-t}v\in H
 \quad\Longleftrightarrow\quad t=0.}
\tag{10}
\]

#### Proof

The squared norm is

\[
 \|V_tv\|^2=\sum_p\frac{p^tF_p}{(\log p)^2}.
\tag{11}
\]

If `t<=0`, then `p^t<=1`, so `(6)` proves convergence.  If `t>0`, then
`p^t/(log p)^2 -> infinity`.  Choose `P_0` such that
`p^t/(log p)^2>=4` for every prime `p>=P_0`.  Then

\[
 \frac{p^tF_p}{(\log p)^2}
 \ge \frac1p
\tag{12}
\]

on that cofinite prime set.  The reciprocal-prime sum diverges, so `(11)` diverges.  This proves
`(9)`.  Applying `(9)` to `t` and `-t` proves `(10)`.
`QED`

### Corollary 3 — exact finite-truncation Cauchy criterion

Let `P_N` be any increasing exhaustion of the ordinary primes by finite sets and let `v_N` be the
corresponding truncation of `v`.  Then

\[
 \boxed{(V_tv_N)_N\ \text{is Cauchy in }H
 \quad\Longleftrightarrow\quad t\le0.}
\tag{12a}
\]

Indeed, orthogonality of the prime coordinates identifies the squared tail distance with the tail
of the nonnegative series `(11)`.  Cauchy convergence is therefore equivalent to summability,
which is Theorem 2.  This holds for every exhaustion; no ordering or averaging freedom remains.

The same statements hold after multiplying every coefficient by an arbitrary nonzero scalar or
by the unit-modulus Xi-height phase.  In particular the nonzero multiplicity-leading Cartier
coefficient cannot hide the wall.

## 3. Exact Route R consequence

For `rho : XiDivisorSupport`, put

\[
 t_\rho=2\operatorname{Re}\rho-1,
 \qquad
 w_\rho(p)=c_\rho\,
   p^{\rho-1/2}\frac{\sqrt{F_p}}{\log p},
\tag{13}
\]

where `c_rho` is the nonzero leading Xi Cartier coefficient.  Phase has modulus one and
`|p^(rho-1/2)|=p^(t_rho/2)`, so Theorem 2 gives the unconditional classification

\[
 \boxed{w_\rho\in\ell^2(\mathbb P)
 \quad\Longleftrightarrow\quad \operatorname{Re}\rho\le\frac12.}
\tag{14}
\]

The reflected coefficient field belongs to the same fixed Hilbert carrier exactly when
`Re rho>=1/2`; both orientations belong exactly on the critical line.

Corollary 3 strengthens `(14)`: for every prime exhaustion, the physical coefficient-faithful
images of the finite truncations are Cauchy exactly when `Re rho<=1/2`.  Therefore a source theorem
asserting only that those images are Cauchy at every Xi fibre already excludes every right-half Xi
divisor.  It then proves the requested statement

```text
forall rho hright,
  burnolCartierDividedShiftHeadFlux (rho : C) <= 0
```

by elimination of the impossible `hright` case, and the existing Route R endpoint closes RH.
No pointwise sign estimate for the Burnol current is needed.

## 4. Heavy conjecture / proof-or-fail loop

### C1 — use the Fisher density itself in one fixed Hilbert completion

`[FAILED; ALREADY CLASSIFIED]`.  The twisted density `p^t F_p` is square summable only for
`t<1/2`.  It cannot see small positive grades, and a common two-orientation carrier exists on
`|t|<1/2`.  This is the fixed-Hilbert Fisher no-go already in the corpus.

### C2 — use the unsmoothed Fisher half-density

`[FAILED]`.  Its squared norm is `sum_p F_p`, which diverges like `sum_p 1/p`.  The correct object
is a singular potential, not the raw half-density.

### C3 — integrate once along the prime-log Cartier direction

`[PROVED]`.  Division by `log p` produces `(1)`.  The vector lies in every strict fractional
prime-log domain `Dom(D^alpha)`, `alpha<1`, but is outside `Dom(D)`.  This is exactly the
source-native singularity required of a first Stokes/Cartier potential.

### C4 — a positive grade may remain admissible because inverse-log damping beats it

`[FAILED]`.  Every positive power eventually dominates every fixed logarithmic power.  The
reciprocal-prime divergence then proves the sharp wall `(9)` for every `t>0`, however small.

### C5 — Xi height phase or Cartier normalization repairs the divergence

`[FAILED]`.  Height phase is unimodular and the Cartier leading coefficient is a fixed nonzero
scalar.  Neither changes membership of `ell^2`.

### C6 — the existing algebraic source-to-Xi chain map automatically supplies the landing

`[FAILED AS AN INFERENCE]`.  Primewise and finite-support coefficient fidelity does not imply that
the physical images of the truncations of `v` are Cauchy.  Claiming this extension without a
source estimate would restate `(14)` and hence RH.

### C7 — strongest survivor

`[PAPER-PROVED]`.  Full fixed-Hilbert comparison is unnecessary.  One canonical vector and one
Cauchy statement suffice.  Unlike the earlier fixed-carrier proposal, this vector works for every
positive grade because the reciprocal-log Cartier potential moves the neutral source just inside
`ell^2` while leaving every positive physical power outside.

## 5. Sharpened remaining producer

The only unproved statement introduced by this theorem is

\[
 \boxed{
 \text{For every Xi divisor }\rho,
 \text{ physical images of the finite truncations of }v
 \text{ are Cauchy in the fixed physical polarization.}}
\tag{15}
\]

It must be derived from pre-divisor Euler--Gamma--Stokes structure.  It is strictly less than a
bounded all-prime intertwiner, a common two-orientation Hilbert comparison, or preservation of an
entire ideal: only one source-selected form-boundary vector is involved.  It is not yet proved;
asserting `(15)` from algebraic coefficient fidelity would be theatre.

## 6. Hostile audit

- **No divisor fitting:** `v`, `D`, and `F_p` are defined before `rho`.
- **No hidden critical-line premise:** Theorem 2 holds for every real grade.
- **No coefficient erasure:** every prime coefficient is positive and the Xi Cartier scalar is
  retained.
- **No exhaustion freedom:** Corollary 3 holds for every increasing finite prime exhaustion.
- **No conflict with the fixed-Hilbert no-go:** that no-go concerns the full Fisher orbit on both
  sides.  The present theorem uses one inverse-log half-density potential and one fixed
  orientation.
- **No RH claim:** `(15)` remains open and is exactly where arithmetic source structure must act.
- **Lean:** deliberately deferred while `HTGeometry` and `RHTower` are being refactored.

## Gates

- [x] source-pure statement and anti-circularity test
- [x] internal corpus and failed-route audit
- [x] seven-step conjecture/falsification loop
- [x] dependency-closed proof of maximal regularity and the exact entrance wall
- [x] exact interface to the Burnol-current endpoint
- [ ] prove the one-vector physical Cauchy landing `(15)` from source Stokes structure
- [ ] formalize after corpus refactor
- [ ] RH

## Log

- 2026-08-08 — fixed-Hilbert Fisher and raw-half-density attempts killed; inverse-log Cartier
  potential discovered and exact one-sided entrance wall proved.
