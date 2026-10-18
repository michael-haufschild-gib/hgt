# Integer jump energy beyond the unit-envelope boundary

- **ID:** thim-integer-energy-beyond-envelope
- **Stage:** 1-in-progress
- **Type:** THEOREM (paper)
- **Scope:** Explicit all-horizon Möbius defect control at endpoint magnitude two,
  including the unit-envelope counterfamily and the entire fifth integer band.

## Plan and gates

1. [x] Reread objective, all README lines, current memories and relevant source; search corpus.
2. [x] Dependency-closed paper proof of integer energy and fifth-band consequence.
3. [x] Formalize path tool, arithmetic transfer, full band and radical/power consequences.
4. [ ] Actual-source Lean/axiom audit, wiring/index/lint, ledger/memory and scratch cleanup.

`update_plan` unavailable; this card tracks work. README is read-only.

## Paper proof [PROVED HERE]

For every integer z, z²≥|z|. Thus an integer-valued path has Dirichlet energy
at least its total variation, hence at least its absolute displacement, with no
path-length loss. If the path starts at one and its next value is zero, the first
edge contributes one; remaining variation pays the terminal magnitude.
For N≥2, the Möbius divisor path has s_N(1)=1 and s_N(2)=0. Therefore, for M≥1,
`E_N(M)≥1+|s_N(M+1)|`. Exact polarization yields
`2D_N(M)≤s_N(M+1)²−|s_N(M+1)|−2`.
Consequently every endpoint of magnitude at most two has nonpositive prefix
defect. Magnitude at most one gives the stronger `D≤−1`. Empty prefixes and
N≤1 have zero defect and are handled separately.

To control the next band, use the exact integer tail cutoff. For
5N<k<6(N+1), only quotients 1,2,3,4,5 occur. If 4 divides k, squarefree
absorption halves the observation into the established unit envelope. Otherwise,
the terminal/two/three deletion combination has magnitude at most one; the
additional prime-five coefficient has magnitude at most one. Hence the damped
response has magnitude at most two throughout 2≤k<6(N+1). At zero damping,
integer energy proves Möbius defect nonpositivity throughout that enlarged range.
Radical/power invariance extends it to unbounded checkpoint families.

In particular every previously constructed response-two endpoint
N=6p−1, k=30p (p prime, p>5), and every positive power of k at the same horizon,
has nonpositive Möbius prefix defect. The endpoint-envelope obstruction is paid
for by integer jump energy; it is not a defect-sign obstruction.

## Baseline, comparison, and limits

Classical ingredients: integer z²≥|z|, triangle inequality, discrete polarization,
Möbius divisor cancellation, and complementary-divisor splitting. Equivalent
classical formulation is the energy bound for the integer path
`k↦Σ_{d|k,d≤N}μ(d)` and its endpoint-magnitude-two defect criterion.
Classification: New formulation, with elementary known constituents labeled.
No external novelty or priority claim. Observation/shifted-correlation baselines:
[TH10](https://arxiv.org/abs/1009.5281), [CMS16](https://arxiv.org/abs/1612.03136).
Exact truncated-sum comparator: Helfgott–Thompson,
[Proposition 3.2](https://link.springer.com/article/10.1007/s40993-022-00408-8).

Broad corpus search returned partial=false, 74104 inventoried files, zero pending,
generation1454379. Ranked candidates/source arguments inspected. Existing path
Poincaré bounds lose a length factor. The neighboring
`CofinalMobiusGradientCoercivityAndRenormalizedDefect.lean` gives finite
odd-squarefree budgets and eventual polynomial-window negativity; this package
instead supplies explicit all-horizon endpoint control and does not import that leaf.
No global all-endpoint sign theorem or positive-damping integer-energy claim is made.

Focused corpus query `integer jump energy endpoint amplitude two fifth band six horizon`
returned partial=false, 74105 inventoried files, zero pending, generation1454404;
compiler coverage mixed. All 20 candidates and 20 source arguments inspected.
The complete scratch proof compiles without warnings: 22 public theorems and
two private helpers. Actual-source and closure audits are pending.
