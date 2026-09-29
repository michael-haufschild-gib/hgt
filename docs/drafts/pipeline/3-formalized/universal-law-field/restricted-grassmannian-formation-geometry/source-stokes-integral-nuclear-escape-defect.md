# Source Stokes integral--nuclear escape defect

- **ID:** ULF-SSIN-001
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Parents:** corpus Stokes jump/scaling laws; `ULF-CFPO-001`
- **Purpose:** construct one source-native object carrying metric magnitude and orientation before
  any zero or divisor is supplied.

## 1. Big-picture interpretation

The prime source already contains an integral charge, but not as a convergent vector at the
critical wall.  It is a unit trace-class ray whose support runs through larger primes while every
fixed prime coordinate disappears.  Positive observation sees its absolute rank-one projection;
the oriented lift remembers from which side of the wall it arrived.

This is the first literal object with all requested properties at once:

```text
pre-divisor + all-prime + cross-prime + reflection-odd
             + nuclear + integral + strongly closed but trace-open.
```

## 2. Definition

For `d>0`, let

```text
pi_d(p)=routePPrimitiveGammaJuliaStokesWallNormalizedWeight d p.       (SSIN.1)
```

The corpus proves

```text
pi_d(p)>0,                  sum_p pi_d(p)=1.                           (SSIN.2)
```

Equivalently, with

```text
j_p(t)=8*t*log(p)*p^(-1-2*abs(t)),
J(t)=sum_p j_p(t),
```

we have `pi_|t|(p)=j_p(t)/J(t)` for `t!=0`.  Thus the normalization uses the
reflection-odd literal prime current itself; no divisor, target eigenvalue, or fitted parameter
enters.

On `H_P=ell2(Nat.Primes)`, define the unit vector

```text
psi_d(p)=sqrt(pi_d(p))                                                    (SSIN.3)
```

and, for nonzero signed horizontal grade `t`, define

```text
mathsf T_src(t)
  = sign(t) |psi_|t|><psi_|t||.                                         (SSIN.4)
```

Set `mathsf T_src(0)=0` only in the strong completion.  Equation `(SSIN.4)` is one
operator field on the punctured grade line, not a family of primewise scalar tests.

Its matrix is

```text
mathsf T_src(t)_(p,q)
  = sign(t)*sqrt(pi_|t|(p)*pi_|t|(q)).                                  (SSIN.5)
```

Every distinct-prime entry is nonzero.  Its diagonal is the unsquared oriented Euler current
`j_p(t)/abs(J(t))`; mixing occurs only after the literal coefficients have been retained.

## 3. Theorem SSIN-A: integral--nuclear oriented unit

For every `t!=0`, `mathsf T_src(t)` is self-adjoint, rank one, trace class, and

```text
mathsf T_src(t)^3=mathsf T_src(t),
abs(mathsf T_src(t))=|psi_|t|><psi_|t||,
Tr mathsf T_src(t)=sign(t) in Z,
||mathsf T_src(t)||=||mathsf T_src(t)||_1=1.                            (SSIN.6)
```

Reflection reverses the operator exactly:

```text
mathsf T_src(-t)=-mathsf T_src(t).                                     (SSIN.7)
```

**Proof.** `(SSIN.2)` gives `||psi_d||^2=1`.  Rank-one operator calculus gives
self-adjointness, trace-class membership, absolute value, norms, and the cubic equation.  Its
only nonzero eigenvalue is `sign(t)`, hence its trace is the same integer.  Since `pi_d` depends
only on positive `d=|t|`, `(SSIN.7)` follows.  QED.

## 4. Theorem SSIN-B: nuclear homotopy on each chamber

The maps

```text
t -> mathsf T_src(t),       t>0,
t -> mathsf T_src(t),       t<0
```

are trace-norm continuous.

**Proof.** On every compact positive `d`-interval, the explicit weights
`log(p)*p^(-1-2d)` have one summable dominating sequence.  Dominated convergence and continuity
of the nonzero normalizing total give `pi_d -> pi_e` in `ell1`.  The Hellinger inequality

```text
sum_p (sqrt(pi_d(p))-sqrt(pi_e(p)))^2
  <= sum_p |pi_d(p)-pi_e(p)|                                           (SSIN.8)
```

gives norm continuity of `psi_d`.  The trace norm of the difference of two unit rank-one
operators is at most twice the norm of their defining vectors.  QED.

Thus each open horizontal chamber carries one honest nuclear homotopy.  The obstruction occurs
only when the wall is adjoined.

## 5. Theorem SSIN-C: strong closure, open trace history

As `t->0` from either side,

```text
psi_|t| -> 0 weakly,
mathsf T_src(t) -> 0 strongly,                                         (SSIN.9)
```

but neither operator norm nor trace norm tends to zero, and

```text
lim_(t->0+) Tr mathsf T_src(t)= 1,
lim_(t->0-) Tr mathsf T_src(t)=-1.                                    (SSIN.10)
```

**Proof.** The corpus wall law gives `J(t)->4` from the right and `J(t)->-4` from
the left.  For each fixed prime, `j_p(t)->0`, so `(SSIN.1)` gives
`pi_|t|(p)->0`, hence every coordinate of `psi_|t|` tends to zero.  Unit norm plus density of
finite-support vectors implies weak convergence to zero.  For fixed `x in H_P`,

```text
||mathsf T_src(t)x||=|<psi_|t|,x>| -> 0,
```

which is strong convergence.  Equations `(SSIN.6)` give the norm and trace statements.  QED.

Consequently every compact observer `K` is blind to the unit:

```text
Tr(mathsf T_src(t) K)
  =sign(t)<psi_|t|,K psi_|t|> ->0,                                    (SSIN.11)
```

because compact operators send bounded weakly-null nets to norm-null nets.

## 6. Exact transgression/conservation identity

Let `q_prime` be the normalized scalar Stokes jump and `q_polar` the normalized
pole--Gamma counterjump.  Existing corpus theorems give `q_prime=1`, `q_polar=-1`, and completed
current charge zero.  The operator lift recovers the prime charge without scalarizing first:

```text
q_prime
  =(1/2)*(lim_(t->0+) Tr mathsf T_src(t)
         -lim_(t->0-) Tr mathsf T_src(t))
  =1,
q_prime+q_polar=0.                                                     (SSIN.12)
```

This fuses three structurally different organs: literal Euler Stokes current, nuclear operator
homotopy, and archimedean pole--Gamma cancellation.  Formation is integral before completion;
completion is information-neutral only because it supplies the opposite oriented unit.

## 7. What this changes

`ULF-CFPO-001` required separate metric and orientation inputs.  `(SSIN.4)` is their canonical
source-side fusion:

```text
metric magnitude = probability ray |psi_d><psi_d|,
orientation       = sign of the linear Stokes current,
fusion            = mathsf T_src(t).
```

It also narrows completion transport.  Any map carrying this charge to the completed
formation defect `mathsf T_D` cannot be continuous only in strong/weak operator topology and
cannot factor through compact observers: `(SSIN.9)`--`(SSIN.11)` would send the source unit to
zero.  It must be a singular relative boundary map that is continuous in the nuclear homotopy
topology on each chamber and retains the wall trace jump.

The exact RH-bearing edge is now

```text
source wall class [mathsf T_src]
  --theta/Poisson relative boundary-->
completed rectangle class [mathsf T_D],                               (SSIN.13)
```

together with domination of the positive target channel by the existing Euler budget `<1`.
This card constructs the left class and proves its unit quantization; it does not assert
`(SSIN.13)`.

## 8. Hostile audit

1. The scalar normalized Stokes jump and probability weights already existed in the corpus.  New
   content is their orientation-faithful, cross-prime, trace-class lift and its topology theorem.
2. A positive projection alone is orientation-blind.  The signed factor in `(SSIN.4)` is forced by
   the linear source current and cannot be dropped.
3. Strong convergence is not a selector; it is the proved obstruction explaining why bounded
   completion reporters lose the charge.
4. Trace one is a unit-cost lower bound, not the desired `<1` upper bound.  Identifying and
   bounding the target image remains open.
5. No claim of a nontrivial corona `K`-class is made; integrality here is the ordinary nuclear
   trace of the signed rank-one fibre.

## Status

Paper proof dependency-closed.  Lean formalization deferred by current read-only research phase.

## Lean certificate

- [x] 2 → 3: Lean `GaloisForLFunctions.HTGeometry.SourceStokesIntegralNuclearUnit`; `lake env lean` + module build pass; axiom audit `[propext, Classical.choice, Quot.sound]` only

Module `GaloisForLFunctions.HTGeometry.SourceStokesIntegralNuclearUnit` (57 constants), axiom-audit clean. It builds on the corpus normalized Stokes weight `routePPrimitiveGammaJuliaStokesWallNormalizedWeight` (positivity, `∑ = 1`), the oriented current `gammaSewnMobiusApertureStokesOrientedFirstTraceCurrent` and its one-sided wall limits `±4`, the polar countercurrent limits `∓4`, and the corpus trace-norm / Schatten API (`RHTower.traceNorm`, `approxNumber`, `HasRankLE`, `memSchattenClass_of_hasRankLE`), `absOp`, `tendsto_inner_lp_of_coord`, and `tendsto_compactOperator_of_weaklyNull_hilbert`. `H_P = ℓ²(Nat.Primes)`; the operator is `InnerProductSpace.rankOne`.

| Claim | Lean declaration |
|-|-|
| (SSIN.1)–(SSIN.2) `π_d > 0`, `∑ π_d = 1`, `π_{|t|} = j_p/J` | `stokesWeight`, `stokesWeight_pos`, `tsum_stokesWeight`, `stokesWeight_eq` |
| (SSIN.3) unit ray `ψ_d = √π_d` | `stokesRay`, `stokesRay_apply`, `norm_stokesRay` |
| (SSIN.4) `T(t) = sign(t)|ψ_{|t|}⟩⟨ψ_{|t|}|` | `sourceStokesUnit`, `stokesProjection` |
| (SSIN.5) matrix `sign(t)√(π(p)π(q))`, every entry nonzero | `inner_single_sourceStokesUnit_single`, `inner_single_sourceStokesUnit_single_ne_zero` |
| diagonal = unsquared oriented current `j_p(t)/|J(t)|` | `inner_single_sourceStokesUnit_single_self`, `gammaSewnMobiusApertureStokesOrientedFirstTraceCurrent_eq_sign_mul` |
| (SSIN.6) self-adjoint, rank one, trace class | `isSelfAdjoint_sourceStokesUnit`, `hasRankLE_sourceStokesUnit`, `memSchattenClass_one_sourceStokesUnit` |
| (SSIN.6) `T³ = T`, `|T| = |ψ⟩⟨ψ|`, `Tr T = sign t`, `‖T‖ = ‖T‖₁ = 1` | `sourceStokesUnit_cube`, `absOp_sourceStokesUnit`, `opTrace_sourceStokesUnit`, `norm_sourceStokesUnit`, `traceNorm_sourceStokesUnit` |
| (SSIN.7) `T(-t) = -T(t)` | `sourceStokesUnit_neg` |
| Thm B trace-norm continuity on each chamber (dominated `ℓ²` continuity of `ψ_d`, rank-two trace-norm bound) | `tendsto_traceNorm_sourceStokesUnit_sub`, `tendsto_stokesRay`, `traceNorm_rankOne_sub_le`, `eventually_stokesWeight_le` |
| (SSIN.9) `ψ_{|t|} → 0` weakly, `T(t) → 0` strongly, norms do not close | `tendsto_inner_stokesRay`, `tendsto_sourceStokesUnit_apply`, `not_tendsto_norm_sourceStokesUnit`, `tendsto_stokesWeight_zero` |
| (SSIN.10) one-sided traces `±1` | `tendsto_opTrace_sourceStokesUnit` |
| (SSIN.11) `Tr(T(t)K) → 0` for compact `K` | `tendsto_opTrace_sourceStokesUnit_comp` |
| (SSIN.12) operator trace jump = normalized prime Stokes jump `1`, polar jump `-1`, sum `0` | `sourceStokes_charge_conservation` |

§7 (SSIN.13) is stated in the card as an open edge and is not asserted. §1 and §8 are interpretation.

## Log

- 2026-09-28 — Lean certificate audited; every numbered claim mapped to a declaration; moved to 3-formalized.
