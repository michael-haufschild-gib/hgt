# Route P primitive base joint-damping wall

- **ID:** `route-p-primitive-base-joint-damping-wall`
- **Stage:** 3-formalized
- **Label:** `P-G185`
- **Source:** P-G184; W-H181 raw modular-conormal trace
- **Statement:** Let `s` be total real damping of the two primitive biorthogonal legs after
  insertion of the P-G181 cubic base self-kernel. The complete regularized prime-depth codiagonal
  is absolutely summable if and only if `s>=0`. Cubic regularization reaches and includes the
  functional-equation reflection wall `s=0`, but no negative-damping neighborhood.

## Conjecture, failure, pivot

P-G184 proved summability exactly on the balanced wall. A natural continuation conjecture was that
the cubic inverse-log regularizer might buy a small open strip across that wall, allowing an
ordinary absolutely convergent contour/Riesz transport to completed Xi. P-G185 falsifies that
conjecture sharply.

For source damping `a+s` and co-source damping `-a`, the product depends only on the total damping
`s`. If `n=p^(e+1)`, define

```text
w_s(p,e)=w_base(p,e) n^(-s),                                      (1)
```

where `w_base` is the P-G181 primitive base weight. Lean proves that the literal regularized
source/co-source coefficient is exactly the complex cast of `(1)` for every split parameter `a`.
The sharp result is

```text
sum_(p,e) w_s(p,e) converges absolutely  iff  s>=0.                 (2)
```

Thus ordinary source-series continuation is retired. The live construction must take a boundary
value at `s=0` and use functional-equation completion, closed graph, distributional transport, or
another non-absolute mechanism without first entering `s<0`.

## Proof of P-G185

The biorthogonal pairing theorem gives

```text
L_(a+s)(p,e) conjugate(R_(-a)(p,e))
 =LSeries.term(Lambda,s+1,n).
```

Factoring `n^(-(s+1))=n^(-1)n^(-s)` and using P-G184 at `s=0` proves the cellwise source identity
with `(1)`.

If `s>=0`, then `n^(-s)<=1` for every primitive cell. Hence

```text
0<=w_s(p,e)<=w_base(p,e),
```

and P-G181 summability proves the forward chamber.

Suppose `s<0`, and set `delta=-s>0`. Restrict to depth-zero primes. The exact cell is

```text
w_s(p,0)=p^delta/[4 p (log p)^2].                                  (3)
```

Every log power is eventually dominated by every positive power, so eventually

```text
(log p)^2<=p^delta.
```

Equation `(3)` is then at least `1/(4p)`. Removing finitely many primes cannot repair
summability, while Euler's prime harmonic series diverges. Therefore the negative chamber is
impossible. This proves `(2)`. `QED`

## New route knowledge

P-G184 and P-G185 together give an exact classification:

- unregularized balanced codiagonal diverges;
- cubic base regularization makes the boundary itself summable and gives total trace `<2`;
- that repair has zero strip width: every negative total damping diverges.

This explains several earlier failures as one universal principle. The functional-equation mate
must be paired *at the modular boundary*. Moving one chamber through the other and hoping absolute
convergence survives is mathematically impossible, even after the exact cubic regularizer.

The result does not prove RH. It changes the live W-H181 theorem from a vague “contour/Riesz
continuation” into a precise boundary-value problem: transport the already-summable `s=0`
codiagonal to completed-Xi conormal residues without requiring a two-sided absolutely convergent
strip.

## Novelty and theatre audit

Internal corpus contains a structurally related sharp inverse-completion wall in
`BurnolAllPrimeCompletionWall.lean`, but for different Burnol prime Cartier coefficients and the
critical line `Re rho=1/2`. It does not identify or classify the P-G181 balanced cubic
source/co-source codiagonal. P-G185 reuses only its elementary power-over-log strategy.

Primary-source audit found general Hardy biorthogonality and trace/inner-function obstructions,
not `(1)`--`(3)`: [Calderaro--Manzur--Noor--Santos](https://arxiv.org/abs/2203.05030) and
[Connes--Consani](https://arxiv.org/abs/1910.14368). No external novelty priority is claimed beyond
the exact Route P source identification and sharp chamber theorem established here.

## Lean certificate

Module:

```text
formal/GaloisForLFunctions/RHTower/RoutePPrimitiveBaseJointDampingWall.lean
```

Capstones:

- `routePPrimitiveBaseJointDampingCodiagonal_eq_weight`;
- `summable_routePPrimitiveBaseJointDampingWeight_of_nonneg`;
- `routePPrimitiveBaseJointDampingWeight_prime_zero`;
- `not_summable_routePPrimitiveBaseJointDampingWeight_of_neg`;
- `summable_routePPrimitiveBaseJointDampingWeight_iff`;
- `summable_routePPrimitiveBaseJointDampingCodiagonal_iff`.

Verification:

- `/tmp/pg185.lean`: `lake env lean /tmp/pg185.lean` passed;
- exact leaf build passed;
- capstone axiom audit: only `propext`, `Classical.choice`, `Quot.sound`;
- targeted forbidden-declaration scan: clean;
- umbrella import wired; umbrella not built.

## Gates

- [x] paper proof dependency-closed
- [x] exact unconditional Lean formalization
- [x] scratch verification
- [x] exact leaf build
- [x] axiom and forbidden-declaration audit
- [x] umbrella wired without umbrella build
- [x] ordinary absolute contour crossing formally excluded
- [ ] source-defined completed boundary-value transport
- [ ] raw conormal trace landing and RH
