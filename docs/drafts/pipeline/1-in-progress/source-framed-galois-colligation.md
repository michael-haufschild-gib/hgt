# The source-framed Galois colligation

- **ID:** `source-framed-galois-colligation`
- **Stage:** 1-in-progress
- **Type:** FOUNDATIONAL HT CONJECTURE / UNIFIED FIELD CANDIDATE
- **Scientific status:** `[CONJECTURE] [GAMMA FINITE SKELETON LEAN-FORMALIZED] [UNFRAMED TORSOR PARENT COLLISION] [NOVELTY OPEN]`
- **Parents:**
  - `source-anomaly-boundary-colligation-field.md`
  - `ht-source-riemann-hilbert-correspondence.md`
  - `gamma-opposite-variance-weyl-seam.md`
  - `hypertranscendental-mackey-corona-field.md`
- **Statement:** The common object is a parameterized source-Galois torsor equipped with its
  opposite-variance boundary colligation and a source-selected analytic framing. The obstruction
  chains are failures of existence, uniqueness, holonomy, transversality, or positive real form of
  that framing reduction.

## 1. Unframed-torsor no-go

Parameterized difference Galois theory already supplies differential-algebraic Galois groups and
torsors for equations such as

```text
sigma(y)=a y.                                              (1)
```

For the additive shift, the natural constant field is the field of period-one meromorphic
functions. In particular, the statement that two Gamma solutions differ by a period-one
multiplier is part of the parent theory and is also Lean-formalized in this project.

Therefore an unframed comparison torsor does not solve the boundary problem. It deliberately
retains the entire periodic gauge and cannot distinguish a canonical analytic source.

## 2. Positive object: a framed torsor with boundary current

Let `P_x` be the minimal parameterized source-Galois torsor of a constrained source `x`. Let

```text
C_x=(alpha_N,beta_N,delta_N,gamma_N,R_N)_N                (2)
```

be its anomaly colligation:

- `alpha_N` is the source-to-observable descent anomaly;
- `beta_N` is outgoing analytic boundary transfer;
- `delta_N` is the boundary self-symbol;
- `gamma_N` is incoming algebraic prolongation defect;
- `R_N` is the algebraic--analytic comparison seam.

The Lean-formalized finite conservation law is

```text
p_N R_(N+1)i_N=R_N+beta_N gamma_N.                        (3)
```

A **source framing** `F_x` is an analytic condition defined before any desired spectrum: asymptotic
normalization, growth class, positivity, domain closure, reflection-compatible boundary value, or
a combination forced by the original constraint. It cuts out a reduction

```text
P_x^F subset P_x.                                         (4)
```

The proposed unified field is

```text
U_x=(P_x,C_x,F_x).                                        (5)
```

It is a constraint object over observable resolution, not a time evolution.

## 3. Gamma/digamma exact model

Before framing, the Gamma solution space is a torsor under nonzero period-one multipliers. On the
additive digamma side, two solutions of the same unit-shift cocycle differ by a period-one
function.

The project already Lean-formalizes a canonical framing:

```text
same digamma cocycle + common logarithmic asymptotic
  => the two sources coincide on the right half-plane.     (6)
```

The explicit digamma source satisfies both properties, so the framed analytic fiber is exactly one
point. Simultaneously, the new finite formalization gives:

```text
analytic Taylor side:       Ind-flat, outgoing beta_N,
algebraic prolongation side: Pro-flat, incoming gamma_N,
comparison current:          law (3).                     (7)
```

Gamma is therefore not a contractible unframed vacuum. It is the first solvable **framing
reduction**: a large periodic torsor reduced to one analytic point while retaining a nonzero moving
boundary current.

## 4. Framed source Riemann--Hilbert conjecture

**[CONJECTURE — FRAMED HT SOURCE RIEMANN--HILBERT]** For every regular source-minimal constrained
HT object, the analytification of its parameterized Galois torsor admits a canonical boundary
colligation `(2)`. Source-natural analytic realizations are equivalent to source framings `(4)`
compatible with `(3)`. This equivalence is fully faithful only when it retains topology, domains,
affine origin, reflection, and the complete source algebra.

The unframed Galois torsor is parent theory. The new claim is that source analysis canonically
selects the allowed framings and that every analytic obstruction realization is a reduction of the
same torsor carrying the same current.

**Falsifiers.** Source-equivalent constraints induce inequivalent framed torsors; two analytic
realizations preserve the unframed Galois group but necessarily carry different currents `(3)`; or
the proposed framing can be changed arbitrarily without changing source data.

## 5. Five-face framing theorem

**[CONJECTURE — FIVE FACES OF ONE REDUCTION]** For a perfect derived framed torsor:

1. **continuation failure:** the reduction `P_x^F` becomes empty on the enlarged domain;
2. **noncanonical boundary conditions:** `pi_0(P_x^F)` has more than one point;
3. **monodromy:** the reduction has nontrivial holonomy or stabilizer transport;
4. **spectral incompleteness:** the tangent complex of the reduction has nonzero homology,
   equivalently the realization is not infinitesimally minimal;
5. **positivity failure:** the reflected reduction has no positive real/polarized point.

This is falsifiable at the level of objects, not spectra. Two chains are representations of one
field only if they induce equivalent reductions preserving `(2)` and `(3)`.

## 6. Capacity--framing complementarity

**[CONJECTURE — INFINITE CAPACITY / THIN FRAMING]** A regular constrained HT source has maximal
differential dimension on its unframed Galois torsor, while the source conormal is finitely
generated over the intrinsic source operator algebra and the cotangent amplitude and boundary-
symbol width of the framing reduction are uniformly finite:

```text
algebraic clock capacity grows without bound,
source framing and transverse current remain perfect and thin.              (8)
```

This is a representation-theoretic version of infinite algebraic clock capacity concentrated on a
thin constraint boundary. Thinness cannot mean finite dimension over the constants: differentiated
consequences of one nonlocal relation are already infinite-dimensional. It means finite generator
rank over the source algebra and uniformly finite transverse boundary width. Hypertranscendence
concerns observables of the clock; thinness concerns the source framing transverse to them.

**Falsifier.** A source-minimal finite-rank constrained HT module whose every intrinsic framing has
unbounded cotangent amplitude or boundary width.

## 7. Framing nontermination conjecture

**[CONJECTURE — HT AS NONTERMINATING FRAMED CURRENT]** Within the regular finite-rank constrained
class, differential algebraicity is equivalent to existence of a faithful source framing for which
the comparison current terminates after finite resolution. Hypertranscendence is equivalent to a
nonempty global framing whose finite comparison current is displaced to arbitrarily high boundary
layers and admits no finite algebraic termination.

The universal Weyl current is not enough: the current must live in the minimal source torsor and
survive source-gauge reduction. Gamma is the affine test; a non-affine coefficient and a nonlinear
source groupoid are required falsifiers.

## 8. Self-dual degeneracy conjecture

Suppose reflection identifies `P_(x^vee)` with the dual of `P_x` and carries framings to reflected
framings.

**[CONJECTURE — SELF-DUAL FRAMING DEGENERACY]** The common degeneracy spectrum is the support where
the reflected framing reduction ceases to be a single transverse positive point. Reflection gives
paired degeneracies; confinement to its fixed locus requires a separate positivity theorem on the
actual tangent complex.

Thus a self-dual zero is not postulated as an eigenvalue. It is a parameter where source framing
loses transverse uniqueness.

## 9. RH pressure test only

**[CONJECTURE; NOT AN RH RESULT]** A zeta source object would have to construct `(5)` from prime and
archimedean constraints before the divisor. The existing RH proof chains may then be different
framing reductions of that same object. Critical zeros would be the common self-dual degeneracy
spectrum of the reduction.

No zero-indexed operator, completed-zeta divisor, or desired spectrum may define `P_x`, `C_x`, or
`F_x`. No zeta framed torsor has been constructed.

## 10. Parent collision and novelty gate

- Parameterized Picard--Vessiot torsors and differential algebraic Galois groups are parent theory.
- Periodic ambiguity of difference equations is parent theory.
- Framed local systems, parabolic structures, Stokes data, boundary triples, and conservative
  colligations are parent languages.
- The Gamma/digamma asymptotic uniqueness theorem is classical source rigidity and not new alone.
- The candidate-new residue is the source-canonical triple `(5)`, the conservation law `(3)` across
  algebraic and analytic realizations, the capacity--framing theorem `(8)`, and a proof of the
  five-face theorem for genuinely different realization categories.

## 11. Topology correction and positive replacement

The finite observable tower cannot itself carry a nonzero separated source constraint. Finite
freedom makes the homogeneous source tangent dense in the raw product topology, so every Hausdorff
product-continuous conormal vanishing on that tangent is zero.

This kills the idea that `(5)` lives in one canonical product completion. The Lean-formalized
positive replacement is that every nonzero source conormal forces a strict minimal refinement of
the clock topology.

**[CONJECTURE]** The actual topology datum in `(5)` is the hypertranscendental Mackey--corona field:
the source-canonical conormal dual pair and its interval of compatible topologies. A framing is a
polarized section of that interval. The five obstruction faces are failures of the same section,
not five properties of one arbitrarily selected topology.

The rank-only capacity--current equality is also rejected as dimension counting. Its positive
replacement is the tail transgression pairing from the finite-rank corona conormal into successive
new algebraic clock cotangent directions, together with opposite-variance seam conservation.

## Gates

- [x] bare unframed torsor rejected as the new object
- [x] periodic solution torsor anchored to existing Lean theorem
- [x] asymptotic digamma framing reduction anchored to existing Lean theorem
- [x] finite anomaly colligation reconstruction Lean-formalized
- [x] opposite-variance boundary-current conservation Lean-formalized
- [x] Gamma incoming and outgoing boundary channels Lean-formalized
- [x] product topology rejected and strict source-conormal refinement Lean-formalized
- [x] rank-only capacity--current equality rejected with transgression-pairing replacement
- [ ] Gamma framed parameterized-Galois/analytic comparison proved
- [ ] one non-affine rank-one framed source treated
- [ ] one nonlinear/nonabelian framed source treated
- [ ] two distinct analytic obstruction categories proved to induce one framing reduction
- [ ] capacity--framing theorem proved
- [ ] independent novelty and significance audit
