# Hodge Theory without Varieties over ℤ (HWV)

Namespace `GaloisForLFunctions.HodgeTheoryWithoutVarieties`; umbrella `HodgeTheoryWithoutVarieties.lean`.
In the review this field was called *the arithmetic Kähler package*. Every theorem is unconditional;
statements named `riemannHypothesis_iff_*` are equivalences and are not proofs of RH.

## 1. Motivation

Every positivity producer in the corpus has one of three types, and each type has a proved limit.

- **Estimates** stop at the detection edge. The universal regime of the complete Weil family ends at
  overlap `(log N)^{1/19}`, and a statement proved without zero information holds for data with
  off-line zeros, so it cannot cross their edge (EHT).
- **Counts** stop short of square-root precision. The coupling equals the kernel, the kernel equals
  the window error of the prime number theorem, and counts with the linear explicit formula cannot
  bound the Hecke defect.
- **Selectors** separate `ζ` from every prime-set flip, but each is a margin on a partial form.

The reformulation theories locate the sign without producing it. EHT shows that positivity fails
through a zero mode. ACoT shows that the coupling is the kernel and that the prime form is an
identity of squares. RIT makes positivity a Hodge index on the primitive part `v₁^⊥`.

A fourth type of producer exists elsewhere: **exact local-to-global positivity with nondegeneracy**.
It proved Hodge–Riemann relations where there is no variety:
- McMullen for simple polytopes, including non-rational ones;
- Adiprasito–Huh–Katz for matroids;
- Elias–Williamson for Soergel bimodules;
- Garland's method for spectral gaps of buildings, computed from their links.

These proofs share one shape. There is a self-similar family of finite-dimensional quadratic forms
with a Kähler class. Local Hodge–Riemann on links or stars gives hard Lefschetz, i.e.
nondegeneracy. A nondegenerate path from a base point where Hodge–Riemann is known then transports
the signature. No step compares a form with a vanishing ground energy, so no step stops at an edge.

HWV builds this package for the divisibility–successor complex of `[1, N]`:
- Weil's form is the intersection form;
- the pole packet is the Kähler class;
- `v₁^⊥` is the primitive part.

RH is the Hodge–Riemann relation on the primitive part, uniformly in `N`, at RH-complete overlap.
The programme has four tasks:
- identify the links, the Lefschetz operator and the base point;
- prove the parts of the package that hold unconditionally;
- locate where the package needs arithmetic input that is not yet available;
- prove that this input is needed.

## 2. Objects

Conventions. Forms are real symmetric matrices `W` on a finite index set. A Kähler class is a vector
`v`. Primitive vectors are those with `⟨x, v⟩ = 0`, with Euclidean orthogonality, as for the pole
hyperplane of the complete Weil matrix. Weil's sign convention holds throughout: Hodge–Riemann means
`W ≥ 0` on primitive vectors.

| Object | Lean | Meaning |
|---|---|---|
| Kähler package | `HodgeRiemann W v`, `StrictHodgeRiemann W v`, `HardLefschetz W v` | `W ≥ 0` on `v^⊥`; `W > 0` on `v^⊥ ∖ 0`; `W` nondegenerate on `v^⊥` |
| Lefschetz path | `t ↦ W t` continuous on a connected parameter space | a deformation of packages |
| Divisibility complex | ACoT `dilationPairs`, `jumpEnergy`, `mertensDiagonal`, `primeDilationForm` | vertices `n ≤ N` with mass `1/n`, dilation edges `(n, kn)` of weight `Λ(k)/k` |
| Affine edges | ACoT `nonRatioWeight`, `shellDegree`, `affineDirichlet` | successor–dilation pairs `(n, kn + h)` at overlap `c` |
| Star of `d` | `star d N` | multiples of `d` in `[1, N]`: the vertices above `d` in the divisor lattice |
| Link of `n` | `linkAdj` | neighbours of `n`, adjacent when their ratio is a prime power |
| In-degree of a weight | `inDegree λ n = (λ ∗ 1)(n)` | Hecke flux into `n` along all dilation edges |
| Star flux | `starFlux λ d m = (λ ∗ 1)(dm) − (λ ∗ 1)(m)` | flux into the star of `d` from outside it |
| Kähler class | RAPT `poleVector`, `normalizedRamanujanHorizonVector 1 N` | the pole packet `F ≡ 1`, `x_n = n^{−1/2}` |
| Intersection form at a resolution | RAPT `completeWeilMatrix φ c N`, `completeWeilEnergy` | Weil's form on atoms of width `c/N` at `log n` |
| Nerve of the star cover | `squarefreeNerve` | sets of primes with product `≤ N` |
| Function-field model | ACS `CurveDatum`; Frobenius kernels | one tower of degrees; links connected |

## 3. Language

- **Kähler package** `(W, v)`: a form with a Kähler class. **Primitive**: orthogonal to `v`.
- **HR / strict HR / HL**: Hodge–Riemann, strict Hodge–Riemann, hard Lefschetz on the primitive part.
- **Lefschetz path**: a continuous family of packages. It is **crossing-free** if HL holds along it.
- **Base point**: a package where HR is known, the start of a deformation.
- **Star** of `d`: the multiples of `d`. **Link** of `n`: its neighbours in the dilation graph.
- **Tower**: the vertices `n p^j`, `j ∈ ℤ`, through `n` for one prime `p`.
- **Commensurable** towers: towers whose degrees lie in one copy of `ℤ`, as for a curve. Over `ℤ`
  they do not, since the numbers `log p` are linearly independent.
- **Boundary flux** of a star: the Hecke weight entering it from outside. **Self-similar
  counterterm**: the flux into every star is constant along the star.
- **Gluing defect**: the part of a form that local statements on a cover do not see.
- **Harmonic packet**: a zero mode of the form on the primitive part. **Liouville property**:
  harmonic packets are trivial.
- **Edge-valid**: true at every resolution, the edge included. An identity, an induction or an
  integer invariant is edge-valid; an estimate against the ground energy is not.

## 4. Mechanisms

**A. Kähler packages.**
1. *Strictness.* HR together with HL is strict HR. A semidefinite form vanishes on a vector only
   when that vector lies in its radical, and HL kills the radical.
2. *Deformation.* Along a Lefschetz path over a connected parameter space, HR at one point implies
   HR everywhere. Strict HR is an open condition, HR is a closed one, and HL makes the two agree.
   The converse is a crossing: a path from strict HR to a failure of HR passes a parameter where HL
   fails.
3. *Lefschetz step.* Adding one atom to a package is a Schur complement. HR survives the step iff
   the innovation of the new atom, i.e. its squared distance to the old span in the form, is
   nonnegative.
4. *Trickle-down* (ALG). A connected Metzler form with positive row sums has one positive square
   iff it has hyperbolic links. Both side conditions are necessary.

**B. The divisibility–successor complex.**
5. *Polarization* (ACoT). `P_N = M_N − J_N`: Weil's prime form is the Mertens diagonal minus the
   graph Laplacian of the dilation complex. Its kernel is the Kähler class (RAPT).
6. *Stars are copies of lower horizons.* The map `m ↦ dm` identifies the dilation graph on
   `[1, ⌊N/d⌋]` with the star of `d`, with all weights divided by `d`. Weil's prime kernel depends
   only on ratios, so the prime form on the star is the prime form at horizon `⌊N/d⌋`.
7. *The counterterm is the boundary flux.* The flux of the weight `λ` into the star of `d` at `dm`
   is `(λ ∗ 1)(dm) − (λ ∗ 1)(m)`. For `Λ` it is `log d` at every vertex, since `Λ ∗ 1 = log`. This
   is exactly the shift `log N − log(N/d)` of the running counterterm. So the renormalized prime
   form on the star of `d` is the renormalized form at horizon `⌊N/d⌋` plus `(log N − log⌊N/d⌋)`
   times the mass.
8. *Stars of the complete family.* Weil's form is translation invariant. On vectors supported on
   multiples of `d`, the complete Weil family at `(c, N)` is therefore the family at
   `(c⌊N/d⌋/N, ⌊N/d⌋)`: the star of `d` is the lower horizon at overlap about `c/d`. This holds for
   every weight, twins included.
9. *Links split into towers.* Two neighbours of `n` in different prime towers have a ratio that is
   not a prime power. The link of every vertex is therefore a disjoint union of cliques, one per
   prime. Towers meet only through the affine edges and through the Kähler class.
10. *The nerve of the star cover.* The stars of the primes cover `[2, N]`. A set of primes meets in
    a common star iff its product is `≤ N`. The nerve is the squarefree complex, and its reduced
    Euler characteristic is `−M(N)`, minus the Mertens function.

**C. Selection.**
11. *The divisor identity selects.* The counterterm is self-similar, i.e. the boundary flux of
    every star is constant, iff `λ ∗ 1` is completely additive. This holds iff `λ` lives on prime
    powers and is constant along each tower. Among unimodular completely multiplicative twists of
    `Λ`, only the trivial twist qualifies.

**D. Calibration.**
12. Over a curve all towers lie in one copy of `ℤ`, so the links are connected and the resolution
    flow is trivial: the edge is `≤ 2g` (EHT). Over `ℤ` the links are disconnected, and the edge is
    unbounded under `¬RH`.

## 5. Questions

1. **Links.** What are the links of the arithmetic complex: finite sieves, coprime residue
   structures or conductor sectors? Which of them satisfy local HR unconditionally?
2. **Lefschetz operator.** Is it the dilation generator, the overlap derivative `∂_c W` or the
   coupling Laplacian `L_pL_q`? For which of them is HL free, and what does it transport?
3. **Shell degree.** Does the shell degree have a Lefschetz-type decomposition that pays it jointly
   with the pole (review Q2b)?
4. **Base point and path.** Can the universal regime serve as the base point and the overlap flow as
   the path?
5. **Function-field model.** Buildings, Ramanujan complexes, or Frobenius acting on commensurable
   towers?
6. **Liouville test.** Must a zero mode on `v₁^⊥` at the first failure of positivity have vanishing
   dilation-jump and affine incidence energies?

## 6. Tools

- Kähler-package calculus: strictness, deformation along connected parameter spaces, the Lefschetz
  step, gluing on covers.
- Star calculus of the divisibility complex: restriction to multiples, boundary flux, self-similar
  counterterms, transfer of the complete family to lower horizons.
- Link analysis of the dilation clique complex; connectivity of links against commensurability of
  towers.
- The nerve of the star cover and its Euler characteristic.
- Liouville theorems: dilation connectivity, successor–dyadic rigidity, Perron sign structure of
  zero modes.
- Interfaces to EHT (edges, crossings, path invariance), ACoT (packet identities, coupling homotopy),
  RAPT (spectral gap, Ramanujan spectrum) and ALG (trickle-down).

## 7. Open research topics

1. A gluing identity for the star cover: an exact formula for the complete Weil form in terms of
   star forms at lower horizons and an explicit gluing term.
2. A joint shell–pole Poincaré inequality on `v₁^⊥` with a constant of degree `< 9` in the overlap.
3. A Lefschetz operator whose hard Lefschetz property is not equivalent to RH, together with a base
   point of index zero.
4. Liouville theorems for zero modes at the edge beyond conductor localization.

## 8. Pillar theorems

| Pillar | Lean | Status |
|---|---|---|
| HR + HL is strict HR; deformation along connected parameter spaces | | target |
| Lefschetz step: HR of an extension is the sign of the innovation | | target |
| Stars are lower horizons for the prime form | | target |
| The counterterm is the boundary flux; renormalized star law | | target |
| Stars of the complete Weil family are lower horizons at overlap `c⌊N/d⌋/N` | | target |
| Links split into tower cliques | | target |
| Nerve of the star cover has reduced Euler characteristic `−M(N)` | | target |
| Self-similar counterterm selects tower-constant weights; among twists only `ζ` | | target |
| Liouville for the dilation Laplacian; Liouville at the edge is RH | | target |
| Commensurable towers have connected links | | target |

## 9. Traps

| Trap | Truth |
|---|---|
| Local HR on every star gives global HR | Positivity on subspaces does not survive sums; the gluing defect carries the index |
| Trickle-down applies to the dilation complex | Its links are disconnected; trickle-down needs connected links |
| Dilation is a Lefschetz operator | It is an isometry onto stars; it transports index and creates none |
| HL along the overlap flow is softer than RH | A crossing-free overlap flow from the universal regime to RH-complete overlap is RH |
| Self-similarity of stars is arithmetic | The geometric self-similarity holds for every weight; only the counterterm selects |

## 10. Context

| Neighbour | Interface |
|---|---|
| EdgeHodgeTheory | edges, crossings, path invariance of inertia, deformation to a model, curve window edge |
| ArithmeticCouplingTheory | Mertens polarization, packet identity at every overlap, shell degree, affine incidence energy, coupling homotopy |
| RenormalizedArithmeticPotentialTheory | complete Weil matrix, pole defect, spectral gap `2 log 2`, Ramanujan spectrum, Hecke covariance of the counterterm |
| ArithmeticLorentzianGeometry | hyperbolic forms, trickle-down, Metzler threshold, Lorentzian closure |
| RenormalizedIntersectionTheory | Hodge index at growing overlap |
| CriticalScaleArithmeticRigidity | successor–dyadic rigidity |
| ArithmeticCastelnuovoSeveri | curve data, scaling surface, Kronecker law |
| SpacingScaleHarmonicAnalysis | Weil's quadratic form and its translation invariance |

## 11. Success criteria

1. **Exactness.** Positivity statements are identities or inductions, valid at the edge.
2. **Local HR.** The links, or stars, carry Lorentzian signature unconditionally.
3. **Arithmetic hard Lefschetz.** An operator or flow parameter along which the form stays
   nondegenerate, with a proof of what it transports.
4. **Level independence.** The induction runs through all levels without loss.
5. **Selectivity** through `Λ ∗ 1 = log`.
6. **Compatibility with the no-gos.** Local forms do not sum, separable assemblies are blind, and
   single towers carry the full index.
7. **Calibration.** Over `𝔽_q` the package reproduces Weil's theorem and fails on the golden datum.

## 12. What counts as a contribution

A contribution proves, in Lean and without hypotheses, one of the following:
- a structural identity of the arithmetic complex (self-similarity, flux, link or nerve law);
- a local Hodge–Riemann statement on an explicit sub-structure;
- a transport theorem with its exact hypotheses;
- an exact boundary, i.e. an equivalence with RH or a no-go with its positive survivor.

Estimates against a ground energy, numerical certificates, and restatements of neighbouring
programmes do not count.
