# Lattice Section Theory of the Scaling Surface (LST)

Namespace `GaloisForLFunctions.LatticeSectionTheory`; umbrella `LatticeSectionTheory.lean`.
Every theorem is unconditional. Statements of the form `riemannHypothesis_iff_*` are proved
equivalences, not proofs of RH.

## 1. Motivation

Weil's proof of RH for a curve `C/𝔽_q` has one engine: Riemann–Roch on `C × C`. Sections are
dimensions, so `h¹ ≥ 0` is free; Riemann–Roch turns that free inequality into the Hodge index,
the Hodge index on the plane of the Frobenius graph is Castelnuovo–Severi, and Castelnuovo–Severi
is `|N − q − 1| ≤ 2g√q`. Sign, precision and selection come out of one identity and one
nonnegativity.

For `ℤ` the corpus has the surface (the scaling surface of ACS: cycles `aH + bV + f`, Weil's
form as the Castelnuovo–Severi defect), the reduction of RH to the existence of an effectivity
with the Riemann–Roch and ample axioms (ACS, AET, RIT), and the refutation of every effectivity
defined from signs. It also has the base: the theta `h⁰` of `Spec ℤ`, a logarithm of a Gaussian
lattice count whose Riemann–Roch `h⁰(d) − h⁰(−d) = d` is Poisson summation (AOG). What it lacks
is Riemann–Roch on the surface for classes with a test component. The doubly exponential aperture
ceiling rules out every producer of the sign that loses a polynomial or exponential factor; an
identity plus a free nonnegativity does not lose anything.

LST is the theory of **sections as lattice counts**: `h⁰` of a class is the logarithm of a
Gaussian-weighted count of lattice points, Serre duality is Poisson summation, and `h¹ ≥ 0` must
come from counting, never from the sign of Weil's form. It asks which lattice and which metric a
class carries, how a two-dimensional Poisson summation can be a surface Serre duality, why the
surface must be the split one, where exactly the primes and the archimedean collar must enter
`h¹`, and how the even integer that RH asks to vanish is read as an index.

## 2. Objects

| Object | Meaning |
|---|---|
| Lattice count | `θ_L(t) = Σ_{x∈L} e^{−πt‖x‖²}` for a full lattice `L` in a Euclidean space of rank `r` |
| Lattice `h⁰` | `h⁰(L, d) = log θ_L(e^{−2d})`: the lattice with metric scaled by `e^{−d}` (an Arakelov bundle of rank `r` over `Spec ℤ`, twisted by degree `d`) |
| Lattice Euler characteristic | `χ(L, d) = r·d − log covol L`: rank times degree plus Arakelov degree |
| Base `h⁰` | `h⁰_ℤ(d) = log Σ_n e^{−πn²e^{−2d}}` (AOG `arithH0`), `χ_ℤ(d) = d`, canonical degree `0` |
| Künneth count | `h_K(x) = h⁰_ℤ(x·H)·h⁰_ℤ(x·V)` on any polar surface: the tensor product of two copies of the base |
| Künneth `h¹`, primitive `h¹` | `h¹_K(x) = h⁰_ℤ(x·H)h⁰_ℤ(−x·V) + h⁰_ℤ(−x·H)h⁰_ℤ(x·V)`; `h¹_prim(x) = ½δ(x, x)` |
| Rectangular lattice | `ℤ²` with `Q_y(m, n) = m² + y²n²`; count `θ(t)θ(y²t)` |
| Completed Epstein function | `Λ_y(s) = π^{−s}Γ(s)Σ'_{(m,n)} Q_y(m,n)^{−s}`, continued by the theta splitting |
| Split plane, boosts | the pole plane `ℤH ⊕ ℤV` (`H² = V² = 0`, `H·V = 1`) with the ample classes `A_u = e^uH + e^{−u}V` |
| Siegel majorant | `P_A(x) = 2(x·A)²/A² − x²`; on the split plane `P_{A_u}(mH + nV) = e^{2u}m² + e^{−2u}n²` |
| Siegel theta of a class family | `Σ_{n∈ℤ^k} e^{−πt P_A(Σ n_i x_i)}` |
| Boost transform | `∫_ℝ F(u) e^{2wu} du` of a function of the boost parameter |
| Primitive `h¹` index | maximal dimension of a primitive subspace on which `h¹_prim < 0` |

## 3. Language

- **Section count**: a function `h ≥ 0` on classes defined from lattice counts or volumes, never
  from the sign of the intersection form.
- **Poisson-dual**: `h(x)` and `h(κ − x)` are exchanged by a Poisson summation; the difference is
  the Euler characteristic.
- **Rank** of a section count along a ray: the slope of `h` in the degree. **Scale**: the Gaussian
  degree `d`.
- **Künneth part / primitive part** of `h¹`: the part fixed by the two fibre degrees, and the part
  carried by the primitive component `x° = x − (x·V)H − (x·H)V`.
- **Soft**: true for every lattice, every characteristic, every datum of a family; hence silent
  about `ζ`.
- **Fake**: a count with every soft property (positivity, Poisson duality, functional equation,
  simple pole) whose zeta function has a zero off the critical line.
- **Boost-equivariant**: depending on the ample class `A_u` only through a Mellin transform in `u`.

## 4. Mechanisms

**A. Lattice counts and Poisson duality.**
1. Poisson summation for a full lattice: `θ_L(t) = covol(L)^{−1}t^{−r/2}θ_{L*}(1/t)`. In degrees:
   `h⁰(L, d) − h⁰(L*, −d) = r·d − log covol L`. This is Riemann–Roch for Arakelov bundles over
   `Spec ℤ`; it is linear in the degree with slope the rank.
2. Poisson plus monotonicity of `θ_{L*}` gives Banaszczyk's inequality `θ_L(t) ≤ (t'/t)^{r/2}θ_L(t')`:
   the slope of `d ↦ h⁰(L, d)` lies in `[0, r]`, tends to `r` at `+∞` and to `0` at `−∞`. The rank
   is the maximal slope of `h⁰`.
3. **Rank law.** Along a ray `nA` of a polar surface the Riemann inequality forces
   `h(nA) + h(κ − nA) ≥ c n²` (Hilbert–Samuel). A lattice count grows at most like
   `rank × degree`, so a count of bounded rank (one fixed lattice, a definite binary form, a Siegel
   majorant of the pole plane) never satisfies the Riemann inequality. The section lattice of a
   class must have rank growing linearly with one degree while its Gaussian scale grows with the
   other.

**B. Künneth Riemann–Roch.**
4. The base is genus one for Riemann–Roch: `χ_ℤ(d) = d`, canonical degree `0`. Its tensor square
   has `κ = 0`, `χ₀ = 0`, `χ(x) = ½x²` — the Riemann–Roch of an abelian surface.
5. For `h_K(x) = h⁰_ℤ(x·H)h⁰_ℤ(x·V)` the base Riemann–Roch gives the exact identity
   `h_K(x) − h¹(x) + h_K(−x) = ½x²` with
   `h¹(x) = h¹_K(x) + ½δ(x, x)`: a Künneth part, positive by Poisson summation, and a primitive part
   equal to half of Weil's form. The quadratic Euler characteristic of the pole plane is paid by
   counting; the whole Hodge index is the primitive `h¹`.
6. Hence the Künneth count satisfies the Riemann inequality iff the Hodge index holds, and it is
   bounded on degree levels unconditionally (the base count decays superexponentially in negative
   degree). On the scaling surface: RH ⇔ the Künneth count is an effectivity.

**C. The definite surface is soft.**
7. A positive definite binary lattice has Poisson duality in two dimensions, a theta function with
   the right functional equation and simple poles, and positivity by construction. For the
   rectangular lattice `Q_y` the theta splitting gives
   `Λ_y(s) = ∫_1^∞(θ_y − 1)t^{s−1} + y^{−1}∫_1^∞(θ_{1/y} − 1)t^{−s} + 1/(y(s − 1)) − 1/s`.
8. On `(1/2, 1)` the pole term `1/(y(s − 1))` drives `Λ_y` to `−∞` at `1`, while at `1/2` the dual
   count contributes `≥ 2 log y − 2 + 2/y`. For `y > e²` the completed Epstein function has a real
   zero in `(1/2, 1)`. Definite Poisson duality therefore selects nothing: the definite surface
   carries fakes.

**D. The split surface selects by its boosts.**
9. The pole plane is the hyperbolic plane. Its Siegel majorant at the ample class `A_u` is the
   rectangular form `e^{2u}m² + e^{−2u}n²`; for `|u| > 1` it is a fake (C). A fixed metric on the
   split plane is a definite lattice and selects nothing.
10. The boost transform of the split counts restores the Euler product:
    `∫_ℝ Σ_{m,n≥1}(e^{2u}m² + e^{−2u}n²)^{−s}e^{2wu}du = c(s, w)·ζ(s + w)ζ(s − w)` with an
    archimedean constant `c(s, w) > 0`. Selection is boost equivariance, i.e. equivariance under the
    scaling flow. The index-`p` sublattice is the boost by `½ log p`, so Hecke operators act on the
    boost transform by `p^{±w}`.

**E. Lorentzian Poisson duality presupposes the sign.**
11. On a polar surface, `P_A(x) = (x·H)² + (x·V)² + δ(x, x)` for `A = H + V` (boosted versions
    likewise). `P_A ≥ 0` everywhere ⇔ the Hodge index.
12. A Siegel theta of finitely many classes converges iff `P_A` is positive definite on their
    integer span. On the scaling surface every finite Siegel theta converges iff RH. A Gaussian
    Poisson summation on the full intersection lattice cannot produce the sign; Zwegers–Vignéras
    completions are the only indefinite alternatives, and their weights cut along the positive cone.

**F. Quantization.**
13. The primitive `h¹` index is the number of negative squares of `δ` on the primitive part, i.e.
    the Hodge defect `κ`: on the scaling surface the number of distinct zeros right of the line.
    It is an even integer, and RH is the statement that it is `< 2`. Any reading of `κ` with
    precision `O(1)` (collision charges, Fredholm indices) is a reading of the primitive `h¹`
    index.

**G. Prime-free cycles.**
14. For tests supported in `(−½ log 2, ½ log 2)` the primitive `h¹` is the archimedean collar plus
    the pole terms; no prime enters. A count realizing this `h¹` would be an effectivity on the
    prime-free subsurface whose Riemann inequality is an identity — the first test of the field.

## 5. Pillar theorems

| Theorem | Status |
|---|---|
| Poisson Riemann–Roch for lattice counts of every rank: `h⁰(L,d) − h⁰(L*,−d) = rd − log covol L` | to prove |
| Banaszczyk slope law: `0 ≤ h⁰(L,d) − h⁰(L,d') ≤ r(d − d')`; rank = asymptotic slope | to prove |
| Rank law: bounded-rank counts violate the Riemann inequality on every polar surface | to prove |
| Künneth Riemann–Roch: `h¹ = h¹_K + ½δ`, `h¹_K > 0`; Künneth count effective ⇔ Hodge index ⇔ RH (scaling surface) | to prove |
| Epstein fakes: the rectangular lattice with `y > e²` has Poisson duality and a real zero in `(1/2, 1)` | to prove |
| Siegel majorant law: `P_A ≥ 0` ⇔ Hodge index; finite Siegel thetas converge ⇔ RH | to prove |
| Boost selection: boost transform of split counts `= c(s,w)ζ(s+w)ζ(s−w)`; Hecke = boost by `½ log p` | to prove |
| Primitive index: primitive `h¹` index = Hodge defect = distinct right zeros; RH ⇔ index `< 2` | to prove |

## 6. Tools

**Available in the corpus.**
- Gaussian lattice Poisson summation in every rank, intrinsic lattices, covolumes and dual lattices
  (`HTGeometry/GaussianLatticeTheta`, `HTGeometry/IntrinsicLatticeTheta`).
- The base theta `h⁰`, its Riemann–Roch, positivity, monotonicity and Mellin transform `Λ(s)`
  (`ArithmeticOrientationGeometry/TheThetaH0OfSpecZ`); theta with characteristic
  (`ArithmeticEffectivityTheory/TheThetaSurface`).
- Polar surfaces, Hodge index, Castelnuovo–Severi, the scaling surface (ACS); the effectivity
  calculus: Riemann inequality, degree boundedness, abundance (AET).
- Pontryagin laws: negative index of Weil's form = distinct right zeros (ACS); RH ⇔ fewer than two
  right zeros (AOG).

**To build in LST.**
- Rank and slope calculus for lattice counts; uniform bounds for base counts in negative degree.
- Künneth calculus of section counts on polar surfaces.
- Two-variable theta splitting, Mellin transforms of products of thetas, real continuation of
  Epstein functions.
- Siegel majorants of polar surfaces and convergence criteria for indefinite Gaussian sums.
- Boost transforms of split counts; Hecke sublattices as boosts.

## 7. Questions

| Question (2.7) | Answer sought |
|---|---|
| What is the section space of a class: which lattice, which metric? | A lattice whose rank grows with one fibre degree and whose Gaussian scale grows with the other (rank law); on the pole plane the tensor square of the base (Künneth count) |
| Is surface Serre duality a two-dimensional Poisson summation for an indefinite lattice? | A Gaussian (Siegel) theta of the intersection lattice exists exactly when the Hodge index holds; on the pole plane, Serre duality is the product of two one-dimensional Poisson summations |
| Why `ζ` and not an Epstein zeta? | Definite binary counts are fakes; the split plane at fixed boost is a definite count; only the boost transform carries the Euler product |
| What is the effectivity of a Hecke correspondence? | The index-`p` sublattice is a boost by `½ log p`; Hecke acts on boost transforms through `p^{±w}` |
| What replaces finite genus? | The base has Riemann–Roch genus one and canonical degree zero; the Künneth part is finite and bounded on degree levels; the infinite part lives entirely in the primitive `h¹` |
| Where must primes and the archimedean collar enter? | In the primitive `h¹ = ½δ`, nowhere else; on prime-free tests only the collar and the poles |
| What is the even integer RH asks to vanish? | The primitive `h¹` index |

## 8. Open research topics

1. A count realizing the primitive `h¹` on prime-free tests (the archimedean collar plus poles) as
   a nonnegative quantity by an identity.
2. The primitive `h¹` on one two-prime Hecke lattice as a sum of squares of coupling differences
   (B7), at every window size.
3. Indefinite (Zwegers–Vignéras) theta counts on the Hecke lattice cut by two ample classes:
   convergence, completion, sign.
4. The degree of a correspondence of `Spec ℤ` as a kernel count, the analogue of
   `deg(m − nF) = #ker(m − nF)` on `E × E`.
5. Height-uniform quantized readings of the primitive index (B40).

## 9. Traps

| Trap | Truth |
|---|---|
| A two-dimensional Poisson summation is surface Serre duality | Definite binary counts have it and are fakes |
| The split plane with a fixed metric is the split surface | It is a rectangular definite lattice |
| The sum of two base `h⁰` is a surface `h⁰` | Its Euler characteristic is `log(D²/2)`; the product is quadratic |
| A bigger lattice gives a surface `h⁰` | Bounded rank means at most linear growth |
| Lorentzian Poisson duality can produce the sign | The Siegel majorant is positive exactly under the Hodge index |
| Künneth Riemann–Roch on the pole plane is progress on the sign | Its `h¹` is positive for free; the primitive part is untouched |

## 10. Context

| Programme | Relation |
|---|---|
| `ArithmeticCastelnuovoSeveri` | the scaling surface, polar-surface calculus, Pontryagin laws; LST supplies section counts for its effectivity axioms |
| `ArithmeticEffectivityTheory` | the effectivity calculus and the theta surface; LST moves from functions of the degree to counts with rank and Künneth structure |
| `ArithmeticOrientationGeometry` | the theta `h⁰` of `Spec ℤ` and pole-plane Riemann–Roch (sum form); LST uses the base and replaces the sum by the tensor product |
| `RenormalizedIntersectionTheory` | quadratic Riemann–Roch with a Serre-dual `h⁰` is the renormalized Hodge index; LST identifies which part of `h¹` carries it |
| `ArithmeticLorentzianGeometry` | Hecke as a boost of the pole plane; LST realizes the boost on lattice counts |
| `HTGeometry` | lattice Poisson summation in every rank |

## 11. Success criteria and contributions

The programme succeeds when the questions of §7 have theorems as answers and when the primitive
`h¹` is either realized as a count on a subsurface where it is not obstructed by zeros (prime-free
cycles, then one prime at a time) or proved not to be realizable by any lattice count there.

A contribution to LST must:
1. define its `h⁰` from counts or volumes, with `h⁰ ≥ 0` by construction;
2. prove its duality by an identity (Poisson-type), not by an estimate;
3. state which part of `h¹` it controls: Künneth or primitive;
4. say what it does on the fakes (definite binary lattices, prime-flip twins, curve data that
   violate RH), since a law that holds on fakes is soft;
5. be unconditional; implications into RH and equivalences must be labelled as such.

## 12. Big picture

The sign problem of RH is the nonnegativity of one `h¹`. On the scaling surface that `h¹` splits:
a Künneth part, which the tensor square of the base pays exactly by Poisson summation, and a
primitive part, which is half of Weil's form. Lattice counts in the definite world have every
soft property and are fakes; the split world selects `ζ` only through its boosts. The field's task
is the primitive `h¹` as a count.
