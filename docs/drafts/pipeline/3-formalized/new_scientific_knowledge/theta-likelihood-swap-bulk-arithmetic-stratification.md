# Theta-likelihood swap bulk has arithmetic normal-crossing stratification

- **ID:** `theta-likelihood-swap-bulk-arithmetic-stratification`
- **Stage:** 3-formalized
- **Type:** `[CANDIDATE NEW SCIENTIFIC KNOWLEDGE] [LEAN-PROVED] [UNCONDITIONAL] [NO RH CLAIM]`
- **Parents:**
  `theta-likelihood-normal-crossing-prime-face.md`,
  `theta-likelihood-ray-boundary-residue.md`
- **Formal target:**
  `formal/GaloisForLFunctions/RHTower/ThetaCuspLikelihoodSwapBulkStratification.lean`
- **Statement:** Temperature-swap symmetrization extends the paired likelihood boundary face into
  the complete two-temperature interior; its zero-temperature corner vanishes exactly on prime
  shells and is strictly positive on composite shells, while every positive-temperature prime
  bulk trace retains strict upper-half-plane orientation.

## Exact claim

Write `S_n(B)` for the scaled likelihood coefficient, `R_n=S_n(0)`, and

```text
Pi_k(B,D;z)=sum_(nm=k) S_n(B)S_m(D) exp(i(log n-log m)z/2).
```

Define the leg-exchange invariant bulk trace

```text
Sigma_k(B,D;z)=Pi_k(B,D;z)+Pi_k(D,B;z).                 (1)
```

The target theorem package is:

1. `Sigma_k(B,0;z)` is exactly the already formalized paired boundary face for every `k`; no
   factor pair is removed.
2. At the corner,

   ```text
   Sigma_k(0,0;z)=2 Psi_k(z),                            (2)
   ```

   where `Psi_k` is the full ray--ray boundary shell.
   Define the real corner mass

   ```text
   M_k=sum_(nm=k) R_n R_m.
   ```

3. For every `k>1`,

   ```text
   Sigma_k(0,0;0)=2 M_k,
   M_k=0  iff  k is prime,
   0<M_k  iff  k is composite.                           (3)
   ```

4. If `p` is prime, then throughout the closed two-temperature quadrant

   ```text
   Sigma_p(B,D;z)
     =[D S_p(B)+B S_p(D)] Phi_p(z),                     (4)
   ```

   with the corresponding derivative identity.  Hence for `B,D>=0`, `B+D>0`, and `Im z>0`, its
   Hermitian current is strictly negative.  One theorem therefore covers both boundary faces and
   the full positive interior.
5. The same factorization and strict current hold for the literal theta-source leg-exchange trace
   at any two points whose intrinsic likelihood coordinates are nonnegative and not both zero.

## Why this is the right frontier object

The common-temperature shell is not a Wigner coordinate.  Leg exchange is forced by the
reflection `(x,y) -> (y,x)` and uses both independent temperatures without identifying them.
Equation (3) prevents a prime-axis quotient from masquerading as progress: the same bulk trace
retains every composite shell and detects it by a nonzero zeroth-order corner mass.  Equation (4)
would be the first exact transport of prime orientation from the normal-crossing boundary into the
full positive two-temperature source interior.

## Hostile audit

- **Arbitrary boundary-to-bulk inference:** not used; `(1)` is an explicit source formula and all
  transport identities are coefficientwise.
- **Composite deletion:** excluded by `(2)`--`(3)`; composites are exactly the shells with positive
  corner mass.
- **Equal-temperature substitution:** absent; `B` and `D` remain independent.
- **RH circularity:** absent; intended inputs are unique factorization, positivity of `R_n` for
  `n>=2`, and existing divisor-phase orientation.
- **Overclaim:** even if proved, this signs only the prime swap-invariant bulk sector.  Higher
  composite currents and the actual corrected endpoint-window current remain open.
- **Preliminary literature verdict:** Hedenmalm's theta spectral problem, Connes' trace/positivity
  programs, horizontal Xi-modulus criteria, and Fourier-transform Wronskian criteria do not state
  `(1)`--`(4)` in the intrinsic theta-likelihood coordinate.  Priority remains provisional.

**Verdict:** `SURVIVES PRELIMINARY ATTACK`.

## Prior-art audit

- Hedenmalm's 2026 theta spectral problem gives the theta-source eigenvalue architecture, but no
  intrinsic likelihood coordinate, leg-exchange normal crossing, or arithmetic corner classifier:
  <https://arxiv.org/abs/2606.17494>.
- Connes' 2026 survey and trace program places positivity and finite Euler products at the RH
  frontier, but does not state the source identity `(1)` or the prime/composite law `(3)`:
  <https://arxiv.org/abs/2602.04022>.
- Sondow--Dumitrescu's horizontal Xi-modulus equivalence and Dimitrov--Xu's transform-Wronskian
  identities concern different carriers and do not imply `(8)`--`(19)`:
  <https://arxiv.org/abs/1005.1104>, <https://arxiv.org/abs/1606.05011>.
- Unique factorization and the abstract prime factor criterion are classical.  Candidate novelty
  is their exact realization as theta-likelihood corner vanishing, together with closed-quadrant
  prime source-current transport.  Priority remains provisional pending independent review.

## Dependency-closed paper proof

Put

```text
g_n=n^2-1,
A_n=exp(-3g_n/2)n^4,
R_n=exp(-3g_n/2)(3/2)n^2g_n,
S_n(B)=exp(-Bg_n)(B A_n+R_n).                            (5)
```

For every integer `n>=1`, `g_n>=0`, hence `R_n>=0`.  Moreover

```text
R_1=0,
R_n>0 for n>=2.                                         (6)
```

The exponential factors are positive, and the last assertion follows from `g_n>0` for `n>=2`.
Likewise, if `n>=2` and `B>=0`, then

```text
S_n(B)>0,                                                (7)
```

because its bracket contains the strictly positive summand `R_n`.

### 1. Boundary and corner restrictions

By definition,

```text
Sigma_k(B,0;z)=Pi_k(B,0;z)+Pi_k(0,B;z)=F_k(B;z),        (8)
```

term by term.  No support restriction occurs.  Since `S_n(0)=R_n`, setting both temperatures to
zero gives

```text
Sigma_k(0,0;z)
 =Pi_k(0,0;z)+Pi_k(0,0;z)
 =2 sum_(nm=k) R_n R_m exp(i(log n-log m)z/2)
 =2 Psi_k(z).                                            (9)
```

At `z=0`, every exponential equals one, so `(9)` becomes

```text
Sigma_k(0,0;0)=(2M_k : C),
M_k=sum_(nm=k)R_nR_m.                                   (10)
```

### 2. Exact prime/composite corner classification

Assume `k>1`.  Every term in `M_k` is nonnegative by `(6)`.

If `k` is prime, every factorization `nm=k` has `n=1` or `m=1`.  Equation `(6)` kills every
summand, so `M_k=0`.

Conversely, if `k` is not prime, the standard factor criterion for a natural number greater than
one supplies `n,m>=2` with `nm=k`.  This pair occurs in the complete positive factor packet.  By
`(6)`, its summand `R_nR_m` is strictly positive; all other summands are nonnegative.  Therefore
`M_k>0`.  We have proved the exhaustive dichotomy

```text
k prime      iff M_k=0,
not k prime  iff 0<M_k,                                 (11)
```

under `k>1`.  This proves `(3)` and shows explicitly that the construction retains composite
coupling rather than projecting to prime axes.

### 3. Prime transport through the closed quadrant

Let `p` be prime.  Its complete ordered factor packet consists of `(1,p)` and `(p,1)`.  Since
`S_1(B)=B`, the swap-symmetrized coefficient on either ordered pair is the same real number

```text
c_p(B,D)=B S_p(D)+D S_p(B).                              (12)
```

It may therefore be pulled outside the complete shell sum, giving

```text
Sigma_p(B,D;z)=c_p(B,D) Phi_p(z),
Sigma'_p(B,D;z)=c_p(B,D) Phi'_p(z).                      (13)
```

Suppose `B,D>=0` and `B+D>0`.  If `B>0`, then `B S_p(D)>0` by `(7)`; if `B=0`, then `D>0` and
`D S_p(B)>0`.  Thus in all cases

```text
c_p(B,D)>0.                                              (14)
```

The already proved divisor-phase theorem gives, for `Im z>0`,

```text
Im(Phi'_p(z) conjugate(Phi_p(z)))<0.                    (15)
```

Substituting `(13)` and using that `c_p(B,D)` is real gives

```text
Im(Sigma'_p conjugate(Sigma_p))
 =c_p(B,D)^2 Im(Phi'_p conjugate(Phi_p))<0              (16)
```

by `(14)`--`(15)`.  This is exact transport from either face through every positive interior
point; no limiting argument or estimate is used.

### 4. Literal theta-source bulk trace

For a real source point `x`, write `B_x` for its intrinsic likelihood coordinate and `C_x>0` for
the boundary desingularizer.  The global atomwise identity already proved in the parent card is

```text
theta_n(x)=C_x S_n(B_x).                                 (17)
```

Define the literal leg-exchange shell by replacing the coefficient of each ordered pair in `(1)`
with

```text
theta_n(x)theta_m(y)+theta_n(y)theta_m(x).
```

Applying `(17)` termwise factors this complete source shell as

```text
C_x C_y Sigma_k(B_x,B_y;z).                              (18)
```

For prime `p`, equations `(13)` and `(18)` give

```text
sourceSigma_p(x,y;z)
 =C_x C_y c_p(B_x,B_y) Phi_p(z),                         (19)
```

and the derivative has the same scalar.  If `B_x,B_y>=0` and `B_x+B_y>0`, then the scalar in
`(19)` is positive by `(14)` and `C_x,C_y>0`.  The same square-scaling argument as `(16)` proves
strict negative current for `Im z>0`.

Equations `(8)`--`(19)` prove every claimed statement using only exact source identities, the
factor criterion for primes, and the already formalized divisor-phase current.  No analytic or RH
hypothesis remains.

## Hostile proof audit

1. `Sigma` is not asserted to equal the complete integrated Wigner current.  It is the exact
   leg-exchange invariant two-point source shell that the real Wigner reflection consumes.
2. Strict orientation is claimed only for prime shells.  Composite corner positivity in `(11)` is
   a mass statement, not an unproved composite current sign.
3. The corner classification excludes `k=1`; at `k=1` the ground--ground coefficient also
   vanishes and would destroy the prime equivalence.
4. Closed-quadrant positivity excludes `(B,D)=(0,0)`; there the prime shell vanishes exactly.
5. Complex positivity is never asserted.  The ordered statement concerns the real mass `M_k`,
   while `(10)` is an equality in `C`.
6. The proof neither deletes endpoint windows nor identifies `B_x` and `B_y`.  Those remain the
   next global-current obstruction.

**Paper verdict:** `[PAPER-PROVED]`.

## Gates

- [x] Internal corpus and failed-route audit
- [x] External parent/noncollision audit
- [x] Hostile category, composite-loss, and circularity audit
- [x] Dependency-closed paper proof
- [x] Exact Lean formalization
- [x] Axiom, module, index, and lint audit

## Open core

`[OPEN CORE]` Determine the strict-current behavior of the nonzero composite corner/bulk residual
and couple it to the corrected endpoint-window current.  The swap-invariant source shell is now
transported exactly; the unsolved object is its composite analytic current plus the actual Wigner
window seam.

## Log

- 2026-07-21 — created in Stage 1 after the equal-temperature category error was replaced by
  leg-exchange symmetrization.
- 2026-07-21 — dependency-closed proof promoted to Stage 2; exact Lean package, targeted build,
  capstone axiom audit, generated indexes, and formal lint passed; promoted to Stage 3.
