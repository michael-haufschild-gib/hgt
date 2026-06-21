# Source-Aware Q0 Alone Reciprocal Positivity

- **ID:** source-aware-q0-alone-reciprocal-positivity
- **Stage:** 2-fully-proven
- **Type:** THEOREM (paper)
- **Source:** `docs/consolidated/revision01/bridge-theorem.md`, RNG-selected formula `[T_{i+j+1}]_{i,j=0}^d`
- **Statement:** For the actual reciprocal seam divisor, all-order positivity of the first shifted tower
  `H_d^(0)=[T_{i+j+1}]_{i,j=0}^d` alone forces every reciprocal atom `y_rho` to lie in `R_{>0}`. Hence,
  with the divisor representation retained, `Q_0[p]>=0` for every real polynomial already implies RH.

## Goal

Separate the source-aware theorem from the source-forgotten moment atlas. For arbitrary moment strings,
the two shifted barriers `Q_0` and `Q_1` are logically independent. For the completed divisor, however,
`Q_0` is not an abstract Hamburger form: it is the quadratic form of the finite complex measure

```text
dnu(y) = y dmu_div(y).
```

This extra source representation lets `Q_0` isolate a bad reciprocal atom.

## Gates

- [x] 0 -> 1 in-progress: well-posed, source-pure, attack idea
- [x] 1 -> 2 fully-proven: complete paper proof, `[PROVED HERE]`, classical pre-1995 approximation input only
- [ ] 2 -> 3 formalized: Lean theorem `<name>`, `lake build` green, `check_axioms.sh` PASS
- [ ] 3 -> 4 publication-ready: standalone note if needed

## Proof

[PROVED HERE]

Let `Y` be the folded reciprocal seam support, with positive multiplicities `M_y`, and define

```text
T_k = sum_{y in Y} M_y y^k,                 k >= 1.
```

For the completed xi divisor, `Y` is conjugation invariant, the multiplicities of conjugate atoms agree,
`Y union {0}` is a countable compact set whose only accumulation point is `0`, and

```text
sum_{y in Y} M_y |y| < infinity.
```

Thus

```text
nu = sum_{y in Y} M_y y delta_y
```

is a finite complex measure, and for every real polynomial `p`,

```text
Q_0[p] = sum_{i,j} c_i c_j T_{i+j+1}
       = sum_{y in Y} M_y y p(y)^2
       = int p(z)^2 dnu(z).
```

If every `y in Y` lies in `R_{>0}`, then `Q_0[p]>=0` is immediate.

Conversely, suppose that some atom `a in Y` is not in `R_{>0}`. We will build a real polynomial with
negative `Q_0`.

The compact set `K=Y union {0}` is countable, hence has empty interior and connected complement. By the
classical Mergelyan approximation theorem, and after symmetrising

```text
p(z) -> (p(z) + conjugate(p(conjugate(z))))/2,
```

every continuous conjugation-symmetric function on `K` is uniformly approximable on `K` by polynomials
with real coefficients.

There are two cases.

1. `a` is real and negative. Since `a != 0` is isolated in `K`, define the continuous symmetric function
   `f(a)=1` and `f=0` on `K\{a}`. Choose real polynomials `p_n -> f` uniformly on `K`. The summability
   of `sum M_y |y|` gives dominated convergence:

   ```text
   Q_0[p_n] -> M_a a < 0.
   ```

   Hence `Q_0[p_n]<0` for all large `n`.

2. `a` is non-real. Then `conjugate(a)` is also an atom with the same multiplicity. Choose a complex
   number `zeta` with

   ```text
   Re(a zeta^2) < 0
   ```

   for instance `zeta=exp(i(pi-arg(a))/2)`. Define the continuous symmetric function

   ```text
   f(a)=zeta,       f(conjugate(a))=conjugate(zeta),
   f=0              on K\{a,conjugate(a)}.
   ```

   Again choose real polynomials `p_n -> f` uniformly. Dominated convergence gives

   ```text
   Q_0[p_n]
      -> M_a a zeta^2 + M_a conjugate(a) conjugate(zeta)^2
       = 2 M_a Re(a zeta^2)
       < 0.
   ```

   So all-order positivity of `Q_0` is impossible.

Therefore `Q_0[p]>=0` for every real polynomial excludes every reciprocal atom outside `R_{>0}`.

Finally,

```text
y_rho = -(rho-1/2)^(-2) in R_{>0}
```

is equivalent to `(rho-1/2)^2` being negative real, hence to `rho-1/2` being purely imaginary. Thus every
zero lies on the critical line. The converse is the direct positive-atom calculation above. This proves

```text
RH  <=>  Q_0[p] >= 0 for every real polynomial p,
```

provided the moments are the source-remembering reciprocal divisor moments.

## Computation

Finite-support interpolation witnesses were generated in:

- `computations/2026-06-21-conway-q0-source-aware-isolation.py`
- `computations/2026-06-21-conway-q0-source-aware-isolation.txt`

The negative-real atom model gives `Q0[p] = -0.4`. The non-real conjugate-pair model chooses a phase so
that `Re(y zeta^2)<0` and gives `Q0[p] = -2.34093998214` up to numerical roundoff. These are finite
analogues of the approximation step in the proof.

## Route Consequence

This does not contradict `shifted-hankel-dual-barrier-independence`: that card concerns arbitrary moment
strings after the divisor representation has been forgotten. The present theorem keeps the source
representation

```text
T_k = sum_y M_y y^k.
```

With that representation retained, the first shifted tower is already faithful. The bridge theorem can
therefore be sharpened into either of two valid targets:

```text
source-forgotten target:  Q_0 >= 0 and Q_1 >= 0;
source-aware target:      Q_0 >= 0 plus the exact reciprocal divisor representation.
```

The second target is strictly smaller as a logical implication to RH. `Q_1` remains useful as the
restricted-domain/raw-form object and as the standard Stieltjes-atlas certificate, but it is not a
logically separate all-order RH implication once `Q_0` is proved for the actual divisor moments.

## Log

- 2026-06-21 -- Conway: created from bridge-theorem RNG node 23, `[T_{i+j+1}]_{i,j=0}^d`.
