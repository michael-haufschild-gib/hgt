# Theta-cusp kernel log-concavity by score-variance domination

- **ID:** `theta-cusp-kernel-log-concavity-score-variance-repair`
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean 4, fully unconditional) / 2026 LITERATURE REPAIR / SOURCE-SPECIFIC POSITIVITY
- **Scientific status:** `[PAPER-PROVED] [LEAN-FORMALIZED] [LOCAL-RESEARCH] [CANDIDATE NEW SCIENTIFIC KNOWLEDGE] [NOVELTY UNVERIFIED]`
- **Parent frontier:** `../../1-in-progress/rh-sota-literature-lean-wall-2026.md`
- **Downstream route:** `../../1-in-progress/hedenmalm-center-mixed-double-positivity-law.md`

## Exact claim

Let

```text
Phi(x)=thetaCuspFullSource(x)
      =sum_(n>=1) phi_n(x),
```

where `phi_n=thetaCuspSourceTerm(.,n)`.  Then, for every real `x`,

```text
Phi''(x) Phi(x)-Phi'(x)^2 < 0.                         (1)
```

Thus the Riemann--Jacobi theta kernel is strictly log-concave on the whole logarithmic line.  The
quantitative first-atom bound is proved first on the nonnegative half-line and transferred globally
by the exact reflection parity.  No
zero-location statement, RH hypothesis, interval arithmetic, or numerical certification enters the
proof.

## Literature audit and repaired wall

`[LITERATURE]` Gershon's June 2026 revision, *On the Log-Concavity of the Riemann Xi Kernel*,
states `(1)` and correctly retracts the earlier claim that log-concavity alone proves RH.  Its
single-atom curvature computation is valid.  The decisive global step is not a completed analytic
proof: the derivative tail estimates are asserted as "analogous", and the claim that the
perturbation ratio improves for every `x>0` is not derived.

The linked Lean artifact does not close this gap.  Its declarations
`perturbation_bound_at_zero` and `perturbation_decreases` are axioms with conclusion `True`, and
`xi_kernel_log_concave_analytic` also concludes only `True`.  The older file similarly represents
the tail-ratio and perturbation steps by trivial `True` theorems.  Hence the artifact is not an
unconditional formalization of `(1)`.

`[OPEN CORE, REPAIRED HERE]` A positive sum of log-concave atoms need not be log-concave.  If
`s_n=phi_n'/phi_n` and `c_n=-(log phi_n)''`, then the exact mixture identity is

```text
(log Phi)'' = Var_p(s_n)-E_p(c_n),
p_n=phi_n/Phi.                                           (2)
```

Individual convexity proves only `c_n>0`; it does not control the score variance in `(2)`.  The
proof below supplies the missing uniform variance domination from the exact theta atom weights.

## Source coordinates

Put

```text
tau=pi exp(2x),                  tau>3,
A_n=tau n^2.
```

For `n>=1` and `x>=0`, the exact Born--Witten identities give

```text
phi_n' = s_n phi_n,
s_n = 9/2 + 3/(A_n-3/2)-2A_n,

phi_n'' = (s_n^2-c_n)phi_n,
c_n = 4A_n+6A_n/(A_n-3/2)^2.                             (3)
```

Since `A_n>3`, elementary rational estimates give

```text
|s_n| <= 2A_n,
4A_n <= c_n <= 3A_n^2,
|phi_n''| <= 7A_n^2 phi_n.                               (4)
```

For the first atom, `(3)`--`(4)` yield the strict curvature budget

```text
phi_1'' phi_1-(phi_1')^2 = -c_1 phi_1^2
                              <= -4 tau phi_1^2.          (5)
```

The exact polynomial comparison, retaining the full `x`-dependent Gaussian rather than freezing
it at `x=0`, is

```text
0 <= phi_n/phi_1
   <= 2 n^4 exp(-tau(n^2-1)).                             (6)
```

## Exact exponential budgets

For `m=4,6,8`, define

```text
A_m=sum_(n>=2) n^m exp(-pi(n^2-1)).
```

The already proved inequalities

```text
exp(-3pi)<1/12000,
16 exp(-5pi)<1/1000
```

and `n=k+2<=2^(k+1)` give geometric majorants, entirely symbolically:

```text
A_4 <= 4/2997,
A_6 <= 4/747,
A_8 <= 8/369.                                            (7)
```

Indeed the three geometric ratios are respectively at most `1/1000`, `1/250`, and `2/125`.

For `d=n^2-1>=3` and `tau>=pi`, the elementary Taylor lower bounds for the exponential give

```text
tau exp(-tau d)   <= 4  exp(-pi d),
tau^2 exp(-tau d) <= 16 exp(-pi d).                       (8)
```

To prove `(8)`, write `y=tau-pi>=0`.  Since `pi<4`,

```text
tau <= 4+y <= 4(1+dy) <= 4 exp(dy),
tau^2 <= (4+y)^2
      <= 16(1+dy+(dy)^2/2) <= 16 exp(dy),
```

and multiply by `exp(-tau d)`.

## Higher-tail estimates

Write `R_j=sum_(n>=2) phi_n^(j)`.  Absolute convergence and `(4)`--`(8)` imply

```text
0 <= R_0 <= (8/2997) phi_1,
tau^2 R_0 <= (128/2997) phi_1,
tau |R_1| <= (256/747) phi_1,
|R_2| <= (1792/369) phi_1.                               (9)
```

For example,

```text
tau |R_1|
 <= 4 sum_(n>=2) n^6 tau^2 exp(-tau(n^2-1)) phi_1
 <= 64 A_6 phi_1,
```

and the other bounds are identical substitutions.

## Global perturbation closure

Expand `Phi=phi_1+R_0`, `Phi'=phi_1'+R_1`, and
`Phi''=phi_1''+R_2`.  Discarding the favorable term `-R_1^2` and applying `(4)` and `(9)` gives

```text
Phi''Phi-(Phi')^2
 <= [phi_1''phi_1-(phi_1')^2]
    +(|R_2|phi_1+|phi_1''|R_0+R_0|R_2|+2|phi_1'||R_1|)

 <= (-4tau+C)phi_1^2,                                   (10)
```

where

```text
C = 1792/369
    +896/2997
    +(8/2997)(1792/369)
    +1024/747
  < 7.                                                   (11)
```

Because `tau>3`, `(10)`--`(11)` give the stronger uniform margin

```text
Phi''Phi-(Phi')^2 <= -5 phi_1^2 < 0.                     (12)
```

The derivation above is first made on `x>0`, where the existing Born--Witten score identities are
available directly.  Every derivative series converges locally uniformly, so both sides of `(12)`
are continuous at `x=0`.  Closure of `(0,infinity)` gives `(12)` at the endpoint as well.  The first
atom is strictly positive there by its explicit formula, completing `(1)` on `[0,infinity)`.

## Lean realization

The unconditional source proof and its exact downstream transfer compile in
`GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspKernelLogConcavity`.  The principal declarations are:

```text
thetaCuspLogConcavityNumerator_neg
thetaCuspLogConcavityNumerator_neg_all
strictConcaveOn_thetaCuspLogSource
thetaCuspFullSource_mul_reflect_le_sq
thetaCuspCenterMixedDensity_le_zero
thetaCuspCenterMixedTwoNodeMatrix_posSemidef
thetaCuspCenterMixedTwoNode_det_nonneg
```

No open proposition, certificate structure, project axiom, `sorry`, computation, or RH hypothesis
occurs in these declarations.

Formal audit complete: exact source leaf passes under `lake env lean`, final module build passes,
the module is imported by the `RHTower` umbrella, and twenty-one load-bearing declarations report
only `[propext, Classical.choice, Quot.sound]`.  Audit includes all three rational tail budgets,
both exponential budgets, first-atom curvature, all higher-tail bounds, endpoint closure, global
reflection, strict concavity, strict mixed-density positivity, midpoint product, two-node positive
semidefiniteness, and determinant nonnegativity.

## Hedenmalm finite positivity consequence

For the center-mixed density

```text
M_a(t)=integral_(0,infinity) r sinh(ar)
         Phi(r/2+t)Phi(r/2-t) dr,
```

log-concavity implies the midpoint-product inequality

```text
Phi(u+t)Phi(u-t) <= Phi(u)^2.
```

Thus `0<M_a(t)<=M_a(0)` for `0<a<1/2`.  Since `M_a` is real and even, every two-node Bochner
matrix

```text
[[M_a(0), M_a(x-y)],
 [M_a(x-y), M_a(0)]]
```

is positive semidefinite.  This is the complete order-two positive-definiteness rung of the
Hedenmalm tangent.  It is strictly weaker than full positive-definiteness, which remains
RH-equivalent.

## Novelty posture

- `[LITERATURE]` Strict theta-kernel log-concavity is claimed in two 2026 preprints.
- `[LOCAL-RESEARCH]` The score-variance repair, exact rational margin `(11)`, and the Hedenmalm
  order-two transfer were not found in the audited sources.
- `[CANDIDATE NEW SCIENTIFIC KNOWLEDGE]` is provisional until a wider primary-source audit confirms
  that these exact mechanisms are absent.
- This card does not claim RH, `TP_infinity`, full Hedenmalm positive-definiteness, or a Hilbert--
  Polya operator.

## Gates

- [x] audit the June 2026 paper and linked Lean artifact
- [x] identify the missing score-variance theorem
- [x] complete a computation-free analytic tail bound
- [x] prove a strict rational curvature margin on paper
- [x] derive the Hedenmalm two-node positive-definiteness consequence on paper
- [x] formalize `(1)` in Lean
- [x] formalize the midpoint-product and two-node Hedenmalm transfer
- [x] direct source, axiom, final-module, and umbrella-reachability audit
- [ ] complete the wider novelty audit

## Primary sources

- Avi Gershon, *On the Log-Concavity of the Riemann Xi Kernel*, version 2, 29 June 2026,
  <https://www.preprints.org/manuscript/202604.0159>.
- Tristen Pierson, *Log-Concavity of the Riemann Xi Kernel and the Riemann Hypothesis*, May 2026,
  DOI `10.5281/zenodo.20465036` (the advertised proof is computation-dependent and its original
  RH implication is not accepted).
- H. Hedenmalm, *Spectral interpretation of Riemann zeta zeros*, arXiv:2606.17494.
