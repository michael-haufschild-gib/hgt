# Route E mesh energy is a classical Mertens mean-square bridge

- **ID:** `ROUTE-E-MESH-MEAN-SQUARE-BRIDGE-001`
- **Stage:** 3-formalized
- **Type:** `[REDISCOVERED]` / `[BRIDGE]` / correction
- **Parent:** `../../1-in-progress/route-e-squarefree-exponential-gibbs-parity.md`
- **RH used:** no
- **Computation used:** no
- **Lean status:** exact finite interpolation and spike-persistence theorems formalized
  unconditionally in `MobiusBlockDefectEnergyInterpolation.lean`

## Corrected statement

Let \(v:\mathbb N\to\mathbb R\), let \(N,h\geq1\), and suppose
\[
 |v(jh+k)-v(jh)|\leq h
 \qquad(0\leq j<N,\ 0\leq k<h).
\tag{1}
\]
Then
\[
 \sum_{j<N}\sum_{k<h}v(jh+k)^2
 \leq
 2h\sum_{j<N}v(jh)^2+2Nh^3.
\tag{2}
\]

For the Mertens function, `(1)` is unconditional because
\[
 |M(b)-M(a)|\leq |b-a|.
\tag{3}
\]
Consequently, on a dyadic interval of length \(U\), a regular width-\(h\) mesh satisfying
\[
 \sum_{j<U/h}M(U+jh)^2\leq U^{2+o(1)}/h
\tag{4}
\]
also satisfies
\[
 \sum_{U<n\leq2U}M(n)^2\leq U^{2+o(1)}+O(Uh^2).
\tag{5}
\]
At \(h\leq U^{1/2+o(1)}\), `(5)` is the all-\(\varepsilon\) Mertens mean-square scale
\(U^{2+o(1)}\).

There is also a sharp bounded-increment spike consequence. If
\[
 |v(k+1)-v(k)|\leq L
\]
and \(2mL\leq |v(0)|\), then
\[
 \sum_{k<m}v(k)^2\geq \frac m4|v(0)|^2.
\tag{6}
\]
Thus a mesh spike of height \(A\), with enough mesh points on one side and mesh-step variation at
most \(h\), forces energy \(\gg A^3/h\). At the Route E energy scale this gives
\[
 A\leq U^{2/3+o(1)},
\tag{7}
\]
not \(U^{3/4+o(1)}\).

## Proof

Write \(a=v(jh+k)\) and \(b=v(jh)\). The identity
\[
 a=b+(a-b)
\]
and \(2b(a-b)\leq b^2+(a-b)^2\) give
\[
 a^2\leq2b^2+2(a-b)^2\leq2b^2+2h^2.
\]
Sum first over \(k<h\), then over \(j<N\), proving `(2)`. Equation `(3)` follows by summing
\(|\mu(n)|\leq1\). Substitution in `(2)` gives `(5)`.

For `(6)`, telescoping and the triangle inequality give
\[
 |v(k)-v(0)|\leq kL\leq mL\leq |v(0)|/2
\qquad(k<m).
\]
The reverse triangle inequality yields \(|v(k)|\geq|v(0)|/2\); squaring and summing gives `(6)`.
Taking \(m\asymp A/h\) gives the lower bound \(\gg A^3/h\), hence `(7)`.

## Frontier verdict

The earlier statement that the mesh law “permits an individual sampled \(M\)-value as large as
\(U^{3/4+o(1)}\)” treated sampled values as an arbitrary array and ignored `(3)`. It is false as a
statement about the actual Mertens function.

More importantly, the mesh law is not a scientifically new source invariant. The local corpus
already records the classical all-\(\varepsilon\) Mertens mean-square criterion
\[
 \sum_{n\leq X}M(n)^2=O_\varepsilon(X^{2+\varepsilon}),
\]
its implication to RH, and its converse from Littlewood on RH in
`mobius-mertens-reversal-energy-rh-criterion.md`. Equations `(2)`--`(5)` place the Route E mesh
criterion inside that existing mean-square family. The exact mesh compression remains useful for
the Gibbs consumer, but it does not manufacture a weaker arithmetic producer.

The classical weak Mertens hypothesis
\[
 \int_1^X(M(t)/t)^2\,dt\ll\log X
\]
is stronger than the all-\(\varepsilon\) scale and is treated in Titchmarsh and in Shōta Inoue,
*Relations among some conjectures on the Möbius function and the Riemann zeta-function*
([arXiv:1705.00853](https://arxiv.org/abs/1705.00853)).

## Strongest positive survivor

`[LEAN-PROVED]` The exact finite mesh-to-full-energy interpolation `(2)` and sharp one-sided
spike persistence `(6)` survive. Their Route E content is diagnostic:

1. the mesh criterion controls more than isolated samples because Mertens increments are bounded;
2. it improves the naïve sampled spike ceiling from exponent \(3/4\) to \(2/3\);
3. it still does not reach exponent \(1/2\);
4. proving the mesh law remains RH-bearing mean-square cancellation, not a new source mechanism.

**Representation lesson.** Further coefficient-norm interpolation cannot move Route E. The next
claim must use ordinary multiplicative breadth to suppress the zero and near-zero Mertens modes,
not rename their energy.

## Formal verification

Module:
`GaloisForLFunctions.RHTower.MobiusBlockDefectEnergyInterpolation`.

Theorems:

- `sq_le_two_sq_add_two_error_sq`;
- `sum_regularGrid_sq_le_sampleEnergy_add_blockError`;
- `abs_sub_zero_le_nat_mul_of_step`;
- `oneSided_plateauEnergy_lower`.

Direct `lake env lean` and targeted module build pass. `#print axioms` reports only
`propext`, `Classical.choice`, and `Quot.sound`.
