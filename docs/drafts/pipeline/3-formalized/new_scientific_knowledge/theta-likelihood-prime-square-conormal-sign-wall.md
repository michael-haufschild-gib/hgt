# Theta-likelihood prime-square conormal sign wall

- **ID:** `theta-likelihood-prime-square-conormal-sign-wall`
- **Stage:** 3-formalized
- **Type:** `[NEW SCIENTIFIC KNOWLEDGE] [UNCONDITIONAL] [NO RH CLAIM]`
- **Parent:**
  `theta-likelihood-swap-bulk-arithmetic-stratification.md`
- **Failed route:**
  `../../5-failed/theta-likelihood-universal-composite-swap-orientation.md`
- **Formal target:**
  `formal/GaloisForLFunctions/RHTower/ThetaCusp/ThetaCuspLikelihoodPrimeSquareSignWall.lean`
- **Statement:** On every prime-square swap shell, reflection-wall current has one exact
  diagonal-versus-endpoint sign wall; its first boundary conormal is strictly positive at every
  positive height, so square shells universally reverse the proposed composite orientation near
  the normal-crossing face.

## Goal

Classify first non-prime shell stratum exactly.  Determine whether composite coupling preserves
prime orientation, and if not, isolate correction forced by square-diagonal mode.  Door passport:
source-pure finite theta-likelihood coefficients; no Xi zeros, RH implication, or numerical input.

## Exact claim

For a prime `p`, set

```text
lambda=log p,
E_p(B,D)=B S_(p^2)(D)+D S_(p^2)(B),
C_p(B,D)=2 S_p(B)S_p(D),
z_p(y)=pi/lambda+i y.
```

Then:

1. The complete factor packet of `p^2` is exactly `(1,p^2),(p,p),(p^2,1)`, and for every `z`,

   ```text
   Sigma_(p^2)(B,D;z)
     =E_p(B,D)[exp(-i lambda z)+exp(i lambda z)]+C_p(B,D),
   Sigma'_(p^2)(B,D;z)
     =i lambda E_p(B,D)[exp(i lambda z)-exp(-i lambda z)].       (1)
   ```

2. If `B,D>=0` and `B+D>0`, then `E_p(B,D)>0` and `C_p(B,D)>0`.  For `y>0`,

   ```text
   J_(p^2)(B,D;z_p(y))
     =2 lambda E_p(B,D)sinh(lambda y)
        [C_p(B,D)-2 E_p(B,D)cosh(lambda y)].                    (2)
   ```

   Consequently

   ```text
   J>0 iff C_p>2E_p cosh(lambda y),
   J=0 iff C_p=2E_p cosh(lambda y),
   J<0 iff C_p<2E_p cosh(lambda y).                             (3)
   ```

3. On boundary face `D=0`, with `R_n=S_n(0)`, the normalized current obeys

   ```text
   lim_(B->0+) J_(p^2)(B,0;z_p(y))/B
     =4 lambda R_(p^2)sinh(lambda y)R_p^2 > 0.                  (4)
   ```

   Hence for every prime `p` and every `y>0`, sufficiently small `B>0` gives strictly positive
   prime-square current.

4. The obstruction has an exact correction.  Remove only the zero-rapidity diagonal amplitude
   `C_p` from the phase, leaving the derivative unchanged, and call the resulting current
   `Jhat`.  Then throughout the same reflection wall,

   ```text
   Jhat_(p^2)(B,D;z_p(y))
     =-4 lambda E_p(B,D)^2 sinh(lambda y) cosh(lambda y) < 0   (5)
   ```

   whenever `B,D>=0`, `B+D>0`, and `y>0`.  Thus the square diagonal is not merely one possible
   source of the sign defect: deleting exactly that stationary mode restores strict orientation.

## Approach

- Classify divisors of `p^2` with `Nat.dvd_prime_pow`; reuse zero-based factor-packet machinery.
- Rewrite complete shell as three modes with exact likelihood coefficients.
- Evaluate modes on reflection wall using complex exponential identities.
- Reduce current to real product `(2)` and use positive endpoint prefactor for iff classifier.
- Use continuity of `S_p` at zero for conormal limit `(4)` and eventual positivity.
- Subtract the unique zero-rapidity diagonal amplitude and prove the restored strict sign `(5)`.

## Hostile audit

- **Composite deletion:** impossible; all three ordered factors are present.
- **Central-mode omission:** explicitly excluded; `C_p` is the term causing reversal.
- **Equal-temperature shortcut:** absent; `B,D` stay independent and obstruction already appears
  on one legitimate boundary face.
- **Sign convention:** current is exactly
  `Im(Sigma' * conjugate(Sigma))`, same convention as parent prime theorem.
- **Asymptotic theatre:** `(4)` is an exact topological limit with explicit positive value, not a
  numerical or big-O estimate.
- **RH circularity:** none; inputs are prime-square factorization, elementary exponential algebra,
  explicit positive theta coefficients, and continuity.
- **Overclaim:** theorem diagnoses raw swap-bulk obstruction.  It does not sign corrected endpoint
  windows or prove RH.  Its diagonal-renormalized sign is currently only on the prime-square
  reflection wall, not on arbitrary composite shells.

**Verdict:** `SURVIVES INTERNAL ATTACK`; paper proof below is dependency-closed.

## Prior-art audit

- Hedenmalm's theta spectral problem supplies parent theta-source architecture but no intrinsic
  likelihood prime-square current or sign wall: <https://arxiv.org/abs/2606.17494>.
- Connes' trace/positivity survey does not state this finite product-fibre obstruction:
  <https://arxiv.org/abs/2602.04022>.
- General Hermite--Biehler theory and weighted divisor-sum literature concern parent classes or
  estimates, not formulas `(1)`--`(4)` for this source-derived carrier.  Search terms included
  weighted divisor exponential phase, semiprime current, prime-square Hermitian current, and
  reflection-wall exponential polynomial.
- Candidate novelty is provisional pending independent review.  Unique factorization and
  hyperbolic-function identities themselves are classical.

## Dependency-closed paper proof

Let `p` be prime.  If `nm=p^2`, then `n` divides `p^2`; the divisor-of-prime-power theorem gives
`n=p^j` with `j<=2`.  Thus `j=0,1,2`, forcing respectively

```text
(n,m)=(1,p^2),(p,p),(p^2,1).                            (5)
```

Conversely all three pairs have product `p^2`, so `(5)` is the exact complete ordered packet.
Its centered logarithmic displacements are `-log p,0,+log p`.  Since `S_1(B)=B`, the first and
last swap coefficients both equal `E_p(B,D)`; the middle equals `C_p(B,D)`.  Substitution into
the finite shell and derivative definitions proves `(1)`.

Prime positivity gives `lambda>0`.  If `B,D>=0` and `B+D>0`, then `S_(p^2)(B)` and
`S_(p^2)(D)` are positive.  At least one of `B,D` is positive, so `E_p>0`; both `S_p` factors are
positive, hence `C_p>0`.

At `z_p(y)`,

```text
exp(i lambda z_p(y))  = -exp(-lambda y),
exp(-i lambda z_p(y)) = -exp(lambda y).                  (6)
```

Using `2cosh t=exp(t)+exp(-t)` and `2sinh t=exp(t)-exp(-t)`, equations `(1)` and `(6)` give

```text
Sigma=C_p-2E_p cosh(lambda y),
Sigma'=2i lambda E_p sinh(lambda y).                     (7)
```

The first expression is real and the second purely imaginary.  Therefore

```text
Im(Sigma' conjugate(Sigma))
 =2lambda E_p sinh(lambda y)[C_p-2E_p cosh(lambda y)],
```

which is `(2)`.  Since `lambda>0`, `E_p>0`, `y>0`, and therefore
`sinh(lambda y)>0`, the prefactor is strictly positive.  Multiplication by it preserves strict
and weak sign, proving all equivalences in `(3)`.

On `D=0`, `S_1(0)=0` and `S_n(0)=R_n`, hence

```text
E_p(B,0)=B R_(p^2),
C_p(B,0)=2S_p(B)R_p.                                    (8)
```

For `B!=0`, substitute `(8)` into `(2)` and divide by `B`:

```text
J(B,0;z_p(y))/B
 =4lambda R_(p^2)sinh(lambda y)
    [S_p(B)R_p-BR_(p^2)cosh(lambda y)].                 (9)
```

The explicit function `S_p(B)=exp(-B g_p)(B A_p+R_p)` is continuous and `S_p(0)=R_p`.
Taking `B->0+` in `(9)` proves `(4)`.  Here `R_p>0`, `R_(p^2)>0`, `lambda>0`, and
`sinh(lambda y)>0`, so the limit is strictly positive.  The defining property of convergence to
a point in the open interval `(0,infinity)` implies that `(9)` is positive throughout some right
neighborhood of zero.  Multiplication by `B>0` then gives `J>0`.

Finally, subtracting `C_p` from the phase in `(7)` leaves `-2E_p cosh(lambda y)` while the
derivative remains `2i lambda E_p sinh(lambda y)`.  Their current is therefore

```text
-4lambda E_p^2 sinh(lambda y)cosh(lambda y).
```

All factors after the leading minus sign are strictly positive under the stated quadrant and
height hypotheses.  This proves `(5)` and identifies an exact orientation-restoring correction.

No dependency remains open on paper.

## Lean formalization

`ThetaCuspLikelihoodPrimeSquareSignWall.lean` proves the complete package:

- exact factor packet and logarithmic displacements;
- exact phase and derivative decompositions;
- reflection-wall phase, derivative, and current identities;
- exact diagonal-renormalized current and its restored strict negative sign;
- strict endpoint and central scale positivity;
- positive, zero, and negative sign-wall equivalences;
- exact boundary quotient and its conormal limit;
- strict positivity of the conormal residue;
- eventual and existential positive-current witnesses on every prime-square shell.

Primary capstones are
`thetaCuspLikelihoodSwapPrimeSquareCurrent_wall_pos_iff`,
`thetaCuspLikelihoodSwapPrimeSquareDiagonalRenormalizedCurrent_wall_neg`,
`tendsto_thetaCuspLikelihoodSwapPrimeSquareCurrent_boundary_div`, and
`exists_thetaCuspLikelihoodSwapPrimeSquareCurrent_boundary_pos`.

## Gates

- [x] 0 -> 1: source-pure statement, exact attack, Door passport, internal audit.
- [x] Dependency-closed paper proof marked `[PROVED HERE]`.
- [x] Hostile proof review: central mode, sign convention, boundary domain, and RH separation audited.
- [x] Exact theorem package formalized in Lean.
- [ ] Publication novelty review remains independent-review work; candidate novelty remains provisional.

## Verification

- Direct `lake env lean` check passes without diagnostics.
- Targeted `lake build GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspLikelihoodPrimeSquareSignWall` passes.
- `#print axioms` on factor classification, raw sign wall, diagonal-renormalized strict sign,
  conormal limit, residue positivity, and positive witness reports only `propext`,
  `Classical.choice`, and `Quot.sound`.
- Generated formal indexes were regenerated and `scripts/formal_tools.py lint --check-generated`
  passed.
- No numerical computation or RH hypothesis enters any proof.

## Log

- 2026-07-21 — Universal composite sign conjecture attacked and killed at prime-square stratum.
- 2026-07-21 — Exact sign-wall classifier and positive conormal residue proved on paper.
- 2026-07-21 — Full exact theorem package formalized in Lean; raw composite orientation route closed.
- 2026-07-21 — Exact zero-rapidity diagonal subtraction proved to restore strict wall orientation.
