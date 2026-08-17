# Sharp metric recurrence exponents for generic local quantum chains

- **ID:** `local-chain-metric-recurrence-exponents`
- **Stage:** 2-fully-proven
- **Type:** PAPER-PROVED BRIDGE / FIRST-RETURN LAW
- **Source:** open core I.5 of
  `../1-in-progress/temporal-codimension-interaction-law.md`
- **Scientific status:** `[PAPER-PROVED USING PUBLISHED METRIC THEOREM] [PRIORITY OPEN]`
- **Imported theorem:** Kleinbock--Margulis extremality of analytic
  nondegenerate manifolds

## Main theorem

Let \(q\geq2\), and let \(\mathcal L_{P_n,q}\) be the full real space of
traceless one-site and nearest-neighbour two-site Hamiltonians on an open
chain of \(n\geq2\) \(q\)-level systems. Put
\[
 D=q^n,\qquad d=D-1.
\]
For a simple-spectrum Hamiltonian, order the eigenvalues and define its
projective gap vector
\[
 g(H)=(E_2-E_1,\ldots,E_D-E_1)\in\mathbb R^d.       \tag{1}
\]

For Lebesgue-almost every \(H\in\mathcal L_{P_n,q}\), the following limits
hold.

For integer-time sampling, let
\[
 T_H^{\rm disc}(r)
 =
 \min\left\{
 k\geq1:
 \left\|k\,\frac{g(H)}{2\pi}\right\|_{\mathbb T^d}<r
 \right\}.                                           \tag{2}
\]
Then
\[
 \boxed{
 \lim_{r\downarrow0}
 \frac{\log T_H^{\rm disc}(r)}{\log(1/r)}
 =d=q^n-1.
 }                                                    \tag{3}
\]

For continuous time, use the first gap as a Poincaré clock and put
\[
 \alpha(H)
 =
 \left(
 \frac{E_3-E_1}{E_2-E_1},\ldots,
 \frac{E_D-E_1}{E_2-E_1}
 \right)\in\mathbb R^{d-1}.                           \tag{4}
\]
Define the first return after at least one winding of that clock by
\[
Q_H(r)
 =
 \min\{q\geq1:\|q\alpha(H)\|_{\mathbb T^{d-1}}<r\}.
                                                               \tag{5}
\]
Define
\[
 T_H^{\rm cont}(r)
 =
 \inf\left\{
 t\geq\frac{\pi}{E_2-E_1}:
 \left\|t\,\frac{g(H)}{2\pi}\right\|_{\mathbb T^d}<r
 \right\}.                                            \tag{5a}
\]
For sufficiently small \(r\), this lower cutoff excludes only the initial
departure near \(t=0\) and forces at least one winding of the Poincaré clock.
The corresponding physical time differs from
\(2\pi Q_H(r)/(E_2-E_1)\) by \(O_H(r)\). Hence
\[
 \boxed{
 \lim_{r\downarrow0}
 \frac{\log T_H^{\rm cont}(r)}{\log(1/r)}
 =d-1=q^n-2.
 }                                                    \tag{6}
\]

If recurrence accuracy is measured by any reporter deficit with a
nondegenerate quadratic minimum at the return point, then phase radius
\(r\asymp\sqrt\varepsilon\). Therefore
\[
 \boxed{
 \lim_{\varepsilon\downarrow0}
 \frac{\log T_H^{\rm disc}(\varepsilon)}
      {\log(1/\varepsilon)}
 =\frac{q^n-1}{2},
 \qquad
 \lim_{\varepsilon\downarrow0}
 \frac{\log T_H^{\rm cont}(\varepsilon)}
      {\log(1/\varepsilon)}
 =\frac{q^n-2}{2}.
 }                                                    \tag{7}
\]

Thus generic local-chain first recurrence has an exact exponent, not only a
volume-density law or worst-case upper bound.

## Lemma 1 — extremality gives an exact first-hit exponent

For \(\beta\in\mathbb R^m\), let
\[
 N_\beta(r)=\min\{q\geq1:\|q\beta\|_{\mathbb T^m}<r\}.
                                                               \tag{8}
\]
If the simultaneous Diophantine exponent of \(\beta\) is \(1/m\), then
\[
 \lim_{r\downarrow0}
 \frac{\log N_\beta(r)}{\log(1/r)}=m.                \tag{9}
\]

### Proof

Simultaneous Dirichlet approximation gives
\[
 N_\beta(r)\leq C_m r^{-m}
 \]
for all sufficiently small \(r\), which proves the limsup bound.

Fix \(\eta>0\). Diophantine exponent \(1/m\) says that only finitely many
\(q\) satisfy
\[
 \|q\beta\|_{\mathbb T^m}<q^{-1/m-\eta}.
 \]
For small \(r\), put \(q=N_\beta(r)\). Then
\[
 q^{-1/m-\eta}\leq\|q\beta\|_{\mathbb T^m}<r,
 \]
and hence
\[
 q>r^{-1/(1/m+\eta)}.
 \]
Letting \(\eta\downarrow0\) gives the liminf bound \(m\). ∎

## Lean progress -- Lemma 1

`formal/GaloisForLFunctions/HTGeometry/SimultaneousDirichlet.lean` (new, umbrella-wired,
axiom-clean) proves Lemma 1's two halves, together with the classical input the upper half needs.

| Card item | Declaration |
|---|---|
| being within `r` of the integer lattice, and its monotonicity | `latticeClose`, `latticeClose_mono` |
| the box subdivision of the unit interval into `Q` parts | `boxIndex`, `boxIndex_lt` |
| two numbers in one box have fractional parts within `1/Q` | `abs_fract_sub_lt_of_boxIndex_eq` |
| **simultaneous Dirichlet approximation**: some `q <= Q^m` is within `1/Q` of the lattice in every coordinate | `exists_simultaneous_dirichlet` |
| the first hitting time `N_beta(r)` | `firstHit` |
| **`(9)` upper half**: `N_beta(r) <= ceil(1/r)^m` | `firstHit_le` |
| **`(9)` lower half**: a multiple that misses the Diophantine radius but hits at `r` forces `q^{-c} < r` | `rpow_lt_of_hit` |
| the exponent form `r^{-1/c} < q` | `rpow_lt_cast_of_hit` |

Simultaneous Dirichlet approximation is *not* in mathlib -- only the one-dimensional statement is --
so it is proved here from the pigeonhole principle on the `Q^m` boxes of side `1/Q`, applied to the
first `Q^m + 1` multiples.

## Lean progress -- Lemma 4

`formal/GaloisForLFunctions/HTGeometry/WindingReturnEquivalence.lean` (new, umbrella-wired,
axiom-clean) proves Lemma 4's equivalence in both directions.

| Card item | Declaration |
|---|---|
| the anchored gap phase in turns, `t g_j/(2 pi)`, and the projective ratios `g_j/g_0` | `gapTurn`, `gapRatio` |
| a continuous `r`-return, and a winding `r`-return at winding `q` | `ContinuousReturn`, `WindingReturn` |
| the anchor phase scales the ratios to the other phases | `gapTurn_zero_mul_gapRatio` |
| **the converse of Lemma 4, exactly**: at `t = 2 pi q/g_0` a winding `r`-return *is* a continuous `r`-return | `continuousReturn_of_windingReturn` |
| **Lemma 4 forward**: a continuous `r`-return gives `\|\|q alpha\|\| < r(1+A)`, with `q` read off the anchor phase | `exists_windingReturn_of_continuousReturn` |
| the winding number is controlled by the elapsed time, `\|q\| <= \|t\|\|g_0\|/(2 pi) + r` | `abs_winding_le_of_continuousReturn` |
| the two-sided statement the exponent argument consumes | `continuousReturn_iff_exists_windingReturn` |

The converse direction is exact -- no `O_H(r)` -- because the anchored phase at the time
`2 pi q/g_0` *equals* `q` times the ratio.  The forward direction costs exactly the factor `1 + A`,
where `A` bounds the ratios; since that is a fixed multiplicative constant on the radius and the
time-to-winding distortion is linear, the logarithmic exponents of the two first-hit functions
coincide.  This is the "time itself supplies one winding direction" step: `d+1` continuous phases
become `d` winding ratios.

## Lean progress -- the reporter-deficit rescaling `(7)`

`formal/GaloisForLFunctions/HTGeometry/QuadraticDeficitRescaling.lean` (new, umbrella-wired,
axiom-clean).

| Card item | Declaration |
|---|---|
| a homogeneous deficit vanishes at the return point | `deficit_zero_of_homogeneous` |
| **the two-sided Taylor comparison** `c dist(z,0)² <= Q_H(z) <= C dist(z,0)²`, by compactness of the unit sphere | `exists_deficit_two_sided_bounds` |
| **`(7)`, one half**: `Q_H(z) <= eps` forces `dist(z,0) <= sqrt(eps/c)` | `norm_le_sqrt_of_deficit_le` |
| **`(7)`, other half**: `dist(z,0) <= sqrt(eps/C)` forces `Q_H(z) <= eps` | `deficit_le_of_norm_le_sqrt` |

The statement is proved for any continuous degree-two homogeneous function that is positive off the
origin -- no Hessian, no smoothness and no explicit quadratic form is needed, only homogeneity and
compactness -- so it covers the card's `Q_H` as soon as its leading Taylor term is isolated.  The
two bounds sandwich the sublevel set `{Q_H <= eps}` between the balls of radii `sqrt(eps/C)` and
`sqrt(eps/c)`, which is exactly "replacing `r` by `sqrt(eps)`": the exponent measured in the deficit
is half the exponent measured in the distance.

### What remains

Lemma 2 (nondegeneracy of the spectral manifold, via the corpus qudit endpoint-extension theorem
plus a discriminant-symmetrised minor) and Lemma 3 (the **imported** Kleinbock--Margulis extremality
theorem, which is not in mathlib and is the card's declared external input).

## Lemma 2 — the local spectral manifold is nondegenerate

On a simple-spectrum chart, regard the centered ordered spectrum as an
analytic map
\[
 F:\mathcal L_{P_n,q}\longrightarrow
 W=\{x\in\mathbb R^D:\sum_jx_j=0\}.                  \tag{10}
\]
The qudit endpoint-extension theorem in
`../3-formalized/nearest-neighbor-qudit-projective-spectral-maximality.md` proves that on one
such chart there is no constant real affine relation among the eigenbranches
except trace.
Consequently the positive-order derivatives of \(F\), up to some finite
order, span \(W\) at some point: otherwise a nonzero covector annihilating
their span would make its pairing with \(F\) locally constant and hence give
an affine branch relation.

This witness can be globalized without choosing an eigenvalue ordering.
Choose finitely many parameter multiindices whose derivative columns span
\(W\) at the witness. Form a maximal minor for one eigenvalue labeling and
multiply its squared value over all \(D!\) labelings. Derivatives of simple
roots are rational functions of the characteristic coefficients and the
discriminant. After multiplication by a sufficiently high discriminant
power, this symmetrized product is a polynomial in the local Hamiltonian
parameters. It is nonzero at the witness. Its zero set is therefore null.

Outside that null set, \(F\) is nondegenerate in the metric-Diophantine
sense. Invertible linear coordinates on \(W\) show that the gap map \(g\) is
nondegenerate. Projectivization on \(E_2-E_1\neq0\) shows that the ratio map
\(\alpha\) is also nondegenerate: an affine relation among its coordinates
would become a linear relation among the gap branches.

## Lemma 3 — metric extremality applies

Kleinbock and Margulis prove that almost every point, with respect to the
parameter measure on an analytic nondegenerate manifold in \(\mathbb R^m\),
has simultaneous Diophantine exponent \(1/m\):

- D. Kleinbock and G. Margulis, *Flows on homogeneous spaces and
  Diophantine approximation on manifolds*, Annals of Mathematics 148 (1998),
  339--360,
  [journal](https://annals.math.princeton.edu/articles/12997).

Apply this theorem to \(g/(2\pi)\in\mathbb R^d\) and to
\(\alpha\in\mathbb R^{d-1}\). Lemma 1 gives `(3)` and the winding-number
form of `(6)`.

## Lemma 4 — winding number equals continuous return time

If all projective phases are within \(r\) of the identity and \(r\) is
small, then
\[
 t(E_2-E_1)=2\pi q+O(r)
\]
for a unique integer \(q\). Substitution in the remaining phases gives
\[
 \|q\alpha(H)\|_{\mathbb T^{d-1}}=O_H(r).
 \]
Conversely, an \(r\)-approximation in `(5)` evaluated at
\(t=2\pi q/(E_2-E_1)\) returns every projective phase within \(O_H(r)\).
The fixed multiplicative constants and the \(O_H(r)\) time correction do
not change a logarithmic exponent. This proves `(6)`.

For a smooth reporter deficit with positive-definite Hessian on the minimal
temporal hull, compactness and Taylor expansion give
\[
 c_H\,\operatorname{dist}(z,0)^2
 \leq Q_H(z)
 \leq C_H\,\operatorname{dist}(z,0)^2
 \]
near the return point. Replacing \(r\) by \(\sqrt\varepsilon\) proves `(7)`.
∎

## What this closes

1. Long-time return density and first return are now separate proved laws.
2. The continuous exponent loses exactly one phase dimension because time
   itself supplies one winding direction.
3. Static nearest-neighbour locality attains the exponent associated with the
   full projective Hilbert dimension.
4. The result is typical in physical coupling space, not in an unrestricted
   random-matrix ensemble.

## Hostile boundary

1. The theorem is almost-everywhere, not a uniform bound for every local
   Hamiltonian.
2. Constants and finite-resolution crossover times remain Hamiltonian
   dependent.
3. Translation-invariant low-parameter families require a separate
   nondegeneracy proof.
4. Continuous spectra, thermodynamic limits and open-system contraction are
   not covered by this finite-chain theorem.
5. Formalization requires a first-principles development of the imported
   metric extremality theorem or a formally proved replacement; no manuscript
   claim is authorized before that dependency is closed.

## Gates

- [x] exact Diophantine-to-first-return lemma
- [x] local spectral nondegeneracy bridge on paper
- [x] discrete exponent
- [x] continuous transverse exponent
- [x] quadratic-deficit conversion
- [ ] exact-object priority audit
- [ ] specialist audit of algebraic symmetrization
- [ ] formal metric-Diophantine dependency

## Lean progress -- the Dirichlet half of `(3)`

`formal/GaloisForLFunctions/RHTower/DiscreteRecurrenceDirichletBound.lean` (new, umbrella-wired,
axiom-clean) proves the upper half of the discrete exponent law, for *every* spectrum, with no
genericity and no metric theory.

| Card item | Declaration |
|---|---|
| the first integer time at which every projective phase is within `r` of an integer | `discreteRecurrenceTime` |
| **the Dirichlet bound** `T^disc(r) <= (⌈1/r⌉ + 1)^d`, from the corpus's simultaneous approximation `exists_fin_simultaneous_integer_approximation_quantitative` | `discreteRecurrenceTime_le_ceil` |
| its real form `T^disc(r) <= (1/r + 2)^d` | `discreteRecurrenceTime_le_pow` |
| **hence `log T^disc(r) <= d · log(1/r + 2)`**, so the exponent is at most `d` | `log_discreteRecurrenceTime_le` |
| the comparison factor `log(N+2)/log N` tends to one, so the bound is asymptotically exactly `d` | `tendsto_dirichletShiftRatio` |

No new pigeonhole was written: the corpus already owned quantitative simultaneous Dirichlet
approximation in `d` coordinates, so this file is the exponent bookkeeping on top of it.

### What remains

The matching *lower* bound, which is where all the content of the sharp law sits.  It holds only
for Lebesgue-almost every `H`, and it is exactly the imported Kleinbock--Margulis extremality of
analytic nondegenerate manifolds: the gap map of the local chain must be shown nondegenerate, and
extremality then rules out the exceptional Diophantine set.  Neither extremality nor the
Khintchine--Groshev transfer it feeds is present in mathlib, so this is the card's genuine formal
gap; the Dirichlet half above needs none of it.
