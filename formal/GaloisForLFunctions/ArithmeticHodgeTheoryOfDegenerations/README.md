# Arithmetic Hodge Theory of Degenerations (AHD)

Namespace `GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations`; umbrella
`ArithmeticHodgeTheoryOfDegenerations.lean`. Every theorem is unconditional. Theorems named
`riemannHypothesis_iff_*` are proved equivalences, not proofs of RH.

## 1. Motivation

The corpus has reduced RH to one even integer: `κ`, the number of distinct zeros right of the
critical line, read on the pole-orthogonal hyperplane `v₁^⊥` of one degenerating family of finite
quadratic forms, the complete Weil matrices `W_{φ,c,N}` (atoms of a profile `φ` of width `c/N` at
`log n`, `n ≤ N`). It has also proved why every producer of positivity met so far stops short:

- **Edge logic.** A statement proved without zero information holds on every datum sharing that
  information, so it stops below the edge of the off-line members; an integer read at an
  RH-complete resolution is RH. Only a statement that holds at the edge *by structure* can cross:
  an identity, an inherited polarization, or an integer with a structural bound.
- **Exclusions.** Estimates lose to the doubly exponential aperture ceiling; soft structure holds
  on the golden fake; local and semilocal pieces and trace carriers `1 − P − P̂` carry no
  positivity; deformation is free; tensor amplification is all-or-nothing; approximation by RH-true
  objects lands in the Laguerre–Pólya class.

Over `𝔽_q` the three proofs of RH rest on objects `ℤ` lacks: intersection numbers that are counts
(Weil), auxiliary sections whose vanishing is counted (Stepanov–Bombieri), and tensor powers of a
realization with Euler products (Deligne). In each of them the sign is a **structure theorem**
(Hodge index on `C × C`), not an inequality. Over `ℤ` the corpus has the algebra of that structure
(correspondences, λ-ring, Rosati involution, Lefschetz traces, theorem of the square), Tate's limit
law naming the missing input (a naive height), and, in ADT, the first piece of its geometry: the
rescaled limit of the complete family is a polarized structure with the dilation semigroup as
monodromy.

**AHD's thesis.** The missing object is an arithmetic Hodge theory of the degeneration of the
scaling surface along the resolution axis: a degenerating polarized family with the dilation
semigroup as monodromy, whose positivity is carried through the critical curve `c^{β+1} ≍ log N` by
one of three carriers —

- **A. a count**: a naive height on correspondences (cardinality or log-count), whose Tate limit is
  Rosati positivity;
- **B. an inherited polarization**: a polarized second-order term of the degeneration at the
  critical curve, inherited by the nearby fibres;
- **C. an integer with a structural bound**: a window index forced to `0` by a source-defined
  sectorial structure —

with one global gluing (one negative square at the pole, distinct primes coupled only through
`∞`) and calibrations over `𝔽_q` and on the fakes. ADT is the first construction (the rescaled
limit). AHD builds the rest: the second-order structure, the carriers, the gluing theorem, and
the calibrations, and it proves exactly which of them can and cannot cross the edge.

## 2. The degeneration and its two scales

The complete family is Weil's form on atomic tests: `W_{c,N}[n,m] = W(g(· − log n), g(· − log m))
/ ∫g²`, `g = φ(·/w)`, `w = c/N`. Weil's form is translation invariant on the zero side: a zero `ρ`
contributes `(n/m)^{ρ−½} · W_ρ(g)` to every entry, so the family is a Gram matrix of the Dirichlet
monomials `n^{ρ−½}` weighted by the atom's spectral weights. Two scales live in it.

- **The bulk** (conductor sector). Ramanujan packets `r_e(n) = c_e(n)/√(φ(e) n log N)` spread over
  the whole range `[0, log N]`. Their energies degenerate like `c^{−β}`; after rescaling they
  converge to the Jordan-totient form (ADT). The bulk is computed by the high zeros `|γ| ≍ N/c`,
  collectively, i.e. by the arithmetic side.
- **The horizon layer** (top block `n ∈ [N/K, N]`). Vectors `n^{−1/2} h(log(n/N))` synthesize the
  test `e^{y/2}h(y)` on a window of length `log K`. They do not degenerate: on the zero side each
  zero contributes `c` times Weil's summand of the synthesized test. The horizon layer is where an
  individual zero is seen.

The **second-order term** at the critical curve is the coupling of the two scales. On the zero side
it splits into a *zero ledger* (the contribution of each individual zero to fixed packets and to
horizon blocks) and the bulk correction (collective). The pole conductor `e = 1` is the only bulk
packet that touches the horizon: its Dirichlet polynomial has the boundary term `N^ρ/ρ`, while for
`e > 1` the boundary terms cancel by `Σ_{d∣e} μ(e/d) = 0`.

## 3. Objects

| Object | Lean | Meaning |
|---|---|---|
| Complete Weil family | RAPT `completeWeilMatrix`, `completeWeilEnergy` | the variation over the resolution plane |
| Zero configuration, Weil summand | Zeta23 `ZeroConfig`, `ZeroConfig.Wsummand`, `ZeroConfig.W` | `W_ρ(f,g) = m_ρ f̂(γ_ρ) conj ĝ(γ̄_ρ)`, the zero side |
| Ramanujan packets | RAPT `normalizedRamanujanHorizonVector`, `ramanujanPoleProfile` | bulk graded pieces |
| Conductor Dirichlet polynomial | `conductorDirichlet` | `D_e(s;N) = Σ_{n≤N} c_e(n) n^{s−1}`, the zero-side reading of `r_e` |
| Horizon term | `horizonTerm` | `[e = 1] N^s/s`: the boundary term of `D_e` |
| Complex Jordan totient | `jordanC` | `J_s(e) = Σ_{d∣e} μ(e/d) d^s`, the constant term `ζ(1 − s)J_s(e)` |
| Zero ledger | `zeroLedger` | contribution of a finite set of zeros to the conductor Gram |
| Horizon block vector | `horizonVector` | `n^{−1/2} h(log(n/N))`, synthesizing `e^{y/2}h(y)` |
| Jordan coefficient, extension data | ADT `jordanCoefficient`, `conductorDeviation` | the limit and the residual channels |
| Critical multiple | `criticalMultiple` | the largest `K` with `J + K X ⪰ 0` for a second-order term `X` |
| Correspondences, Rosati form, naive height | AET `intRosatiForm`, `tateLimit`; AOG `Correspondence` | carrier A |
| Lévy jump count, creation potential | LST `jumpCount`; `primeJumpCount`, `creationPotential` | the count with prime atoms |
| Glued state, gluing determinant | AKG `archGlue`; ADT `redhefferMatrix` | the one negative square |
| Window index | WD `fredholmIndex`, `wienerHopfLift` | carrier C |
| Fakes | ACS `goldenDatum`; LST Epstein lattices; ADT prime-flip twins | control |

## 4. Language

- **Resolution** `(c, N)`; **universal regime**, **edge**, **RH regime** as in EHT.
- **Critical curve**: `c^{β+1} = K log N` (`c⁸ = K log N` for the tilted spline, `β = 7`); `K` is its
  **multiple**.
- **Bulk / horizon layer**: Ramanujan packets of fixed conductor / vectors supported in
  `[N/K, N]`.
- **Second-order term**: the limit of `c^β` times the extension data along the critical curve.
- **Zero ledger**: the second-order contribution of a fixed finite set of zeros.
- **Horizon term** of a packet: the coefficient of `N^ρ/ρ` in its Dirichlet polynomial at `ρ`.
- **Seen by a packet**: a zero whose ledger entry on that packet is not `o(c/log N)`.
- **Carrier**: count (A), inherited polarization (B), integer with a structural bound (C).
- **Creation potential**: `−2Σ_{n<e^{2a}} Λ(n)/√n`, the mass the prime atoms cost in the jump count.
- **Gluing**: a coupling through the pole by a rank-one or one-hyperplane term.
- **Fake**: a datum on which every soft law holds and RH fails.

## 5. Mechanisms

**A. Count.** naive height ⇒ Tate limit `≥ 0` ⇒ Rosati positivity at a cycle ⇒ orbit Hodge index
⇒ RH (AET, AOG). Weil's form of a test is the Lévy jump count of the Gamma factor, plus jumps across
the prime gaps `log n` with weight `Λ(n)/√n`, plus the constant `Ω(0)`, the creation potential and
the pole term. A count pays when its jumps pay the constant, the creation potential and the pole.

**B. Degeneration.** rescaled limit (Jordan) ⇒ second-order term at the critical curve ⇒
polarized? ⇒ inheritance through the critical curve ⇒ HL on the positive locus ⇒ RH. The zero side
splits the second-order term into the zero ledger and the bulk correction: on fixed conductor
packets the horizon terms cancel except at the pole, so an individual zero enters only through the
pole conductor, with the weight `m_ρ/(ρ(1 − ρ))`, positive on every reflection quadruple. On
horizon blocks a zero enters through Weil's summand of the synthesized test. Fixed packets cannot
see a zero; horizon blocks can.

**C. Integer.** source-defined sectorial multiplier ⇒ window index `0` on every window ⇒ RH (WD).
An integer crosses the edge only with a bound below `2` that holds by structure.

**G. Gluing.** One rank-one gluing at the pole creates the Mertens function (Redheffer) and the one
extra negative square (`κ + 1`, AKG). Positivity is never semilocal: distinct primes couple only
through `∞`.

**Cal. Calibration.** Over `𝔽_q` the monodromy is finite and detection happens at window `2g`; the
zero ledger is configuration-general, so selection must come from the bulk or from a carrier.

## 6. Questions the programme aims to answer

1. What is the second-order term of the degeneration at the critical curve, and which structure
   polarizes it? How do the zeros enter it?
2. Which packets can see a zero at the critical curve: fixed conductors, growing conductors,
   horizon blocks?
3. What set does `τ_x(ξ ⋆ ξ′)` count, up to bounded error? What are Stepanov's auxiliary sections on
   the scaling surface?
4. How do the prime atoms of the jump measure enter a count, and what pays the creation potential?
5. Which lattice carries the sections of a class of degree `a` (rank `≈ e^{2a}`), with which metric?
6. What is the logarithmic completion of the isotropic count (Voronoi), and does it commute with
   boost averaging?
7. Why `ζ` and not an Epstein function, the golden fake or a prime-flip twin?
8. Which gluing creates exactly one negative square, and which couplings between primes are
   allowed?
9. Which integer has a structural bound, and at which resolution is it read?

## 7. Tools it aims to develop

- Zero-side calculus of the complete family: translation law of Weil summands, packet Dirichlet
  polynomials, horizon terms, complex Jordan totients, zero ledgers.
- Second-order (critical-multiple) calculus: limits along the critical curve, the interval of
  admissible multiples, the critical multiple as a generalized eigenvalue.
- Nilpotent-orbit and `SL₂`-orbit theorems (Schmid, Cattani–Kaplan–Schmid) as formal models.
- Néron–Tate theory on `ℤ[ℚ_{>0}^×]`; Arakelov `h⁰` (van der Geer–Schoof, Bost) on lattices of
  growing rank.
- Lévy–Khintchine and Dirichlet forms on intervals with prime atoms; Slepian / Landau–Widom.
- Zwegers–Vignéras indefinite theta, Voronoi summation.
- Wiener–Hopf / Szegő factorization; λ-rings and Adams operations; Stepanov's method;
  function-field calibration (curve windows, elliptic adeles over `𝔽₃`).

## 8. Pillar theorems

| Pillar | Lean | Status |
|---|---|---|
| Translation law: each zero contributes `(n/m)^{ρ−½} W_ρ(g)` to the family | — | target |
| Conductor Dirichlet polynomials: exact Möbius splitting and horizon-term law | — | target |
| Zero ledger of fixed packets: rank one at the pole, weight `m_ρ/(ρ(1−ρ))`, positive per quadruple | — | target |
| Zero ledger of horizon blocks: Weil's summand of the synthesized test | — | target |
| Critical-multiple calculus | — | target |
| Prime atoms in the jump measure; creation potential | — | target |
| Gluing index theorem | — | target |
| Calibration: the ledger is configuration-general | — | target |

## 9. Open research topics

1. The bulk correction at the critical curve: the collective `1/log N` term of the high zeros, read
   on the arithmetic side.
2. The coupling of bulk and horizon layer (growing conductors `e ≍ N/K`).
3. Polarization of the second-order term by the dilation monodromy (`SL₂`-orbit type inheritance).
4. The count of the whole prime-free window (Lévy Poincaré inequality, pole signs) and the first
   Hecke graph (`T₂`).
5. Naive heights on correspondences of bounded degree.
6. The integer: a sectorial multiplier at logarithmic resolution on a positive proportion of
   windows.
7. Calibration over `𝔽_q(T)`; limits of the fakes.

## 10. Traps

| Trap | Truth |
|---|---|
| The rescaled limit polarizes the edge | It is zero-blind; zeros enter at the quantum `1/log N` (ADT) |
| Fixed packets will see an off-line zero at the critical curve | Their horizon terms cancel except at the pole, where every quadruple contributes positively |
| The second-order term is one more estimate | It is an identity on the zero side; its sign is structure, its size is not the issue |
| A count built from the base sees the sign | Bidegree counts are constant on primitive classes (LST) |
| A trace identity is positivity | `1 − P − P̂` is negative on time-limited vectors |
| Local positivity glues | One rank-one gluing creates `M(N)` and one negative square |
| Soft laws select | They hold on the golden fake and Epstein lattices |

## 11. Context

| Neighbour | Interface |
|---|---|
| ArithmeticDegenerationTheory | rescaled limit, monodromy, weight strings, inheritance radius, Redheffer gluing: the first construction of the field |
| EdgeHodgeTheory | edge logic, windows, crossings, integer readings |
| HodgeTheoryWithoutVarieties | stars, gcd strata, cross-conductor deviation bound |
| RenormalizedArithmeticPotentialTheory | complete Weil matrix, packets, completed conductor energies |
| ArithmeticOrientationGeometry, ArithmeticCastelnuovoSeveri | scaling datum, configurations, orbit correlations, golden fake |
| ArithmeticEffectivityTheory | naive heights, Tate limit law, Stepanov over `ℤ` |
| LatticeSectionTheory | lattice `h⁰`, Künneth RR, jump counts, Epstein fakes |
| AdelicKreinGeometry | glued archimedean state, index `κ + 1` |
| ConjugateDiagonalGeometry (WD) | window index, Szegő factorization |
| Zeta23 | zero configurations and Weil summands |

## 12. Success criteria

The field is developed when it has (i) the second-order term at the critical curve identified on
the zero side, with the packets that see a zero classified; (ii) a count that reads the primes
inside the jump measure, with its creation potential paid on an explicit window; (iii) a gluing
theorem with exactly one negative square; (iv) an integer with a structural bound or a proof that
none exists at a given resolution; (v) calibrations that separate `ζ` from the fakes.

## 13. What counts as a contribution

A contribution is an unconditional Lean theorem in this folder, wired into the umbrella, that
meets at least one of the criteria below and says which kind of statement it is (identity,
inherited polarization, integer invariant, estimate with its regime, equivalence, or no-go with its
positive survivor).

1. `h⁰` from arithmetic counts; `h¹ ≥ 0` because it is a dimension, a cardinality or a log-count.
2. A Riemann–Roch identity at every degree by a Poisson-type duality on lattices of growing rank.
3. Primitive `h¹` of a test class `= ½W(f, f)`; for graph classes a height equal to the Lefschetz
   trace up to bounded error.
4. A degeneration statement: rescaled limits, second-order terms, inheritance, zero ledgers.
5. Calibrations over curves, on prime-free cycles, on the fakes.
6. It avoids the proved no-gos: cones, bidegree counts, fixed rank, definite counts, Siegel
   majorants at a fixed boost, ordinary Poisson pairs for the isotropic count, semilocal positive
   carriers, trace carriers `1 − P − P̂`, separable gluing, free deformation.
7. Selection: it fails for the golden fake, prime flips and Epstein lattices beyond the self-dual
   point, and reproduces Weil and Stepanov over `𝔽_q`.
8. Gluing: global, one negative square at the pole, distinct primes coupled through `∞`.
9. Consistency with quantization: the defect it forces to zero is the window index.

Restatements of neighbouring programmes and numerical certificates do not count.
