# Prime-source ferromagnets, Lee--Yang closure, and RH

- **ID:** `prime-source-ferromagnetic-ising-lee-yang-limit-rh`
- **Stage:** 1-in-progress
- **Type:** `[LARGE OUTLANDISH DETOUR] [CONJECTURE] [FORMALIZED FINITE CONSUMER]`
- **Lean inputs:** `formal/GaloisForLFunctions/RHTower/LeeYangQuadraticBlock.lean`,
  `formal/GaloisForLFunctions/RHTower/EulerReciprocalLeeYangNoGo.lean`,
  `formal/GaloisForLFunctions/RHTower/PrimeWordEnsembleBoundaryTomography.lean`,
  `formal/GaloisForLFunctions/RHTower/PrimeSupportMultivariateLiftMarker.lean`, and
  `formal/GaloisForLFunctions/XiLaguerrePolya.lean`
- **Prior no-go:** `../0-backlog/lee-yang-localization.md`
- **Statement:** `[CONJECTURE]` A cofinal family of finite ferromagnetic Ising partition polynomials,
  constructed functorially from the completed prime source, has Cayley transforms converging locally
  uniformly to a zero-free entire factor times centered Xi.  Lee--Yang localization at every finite
  stage then forces RH at the marginal limit.

## Goal and the positive repair of the old marginality theorem

The earlier Lee--Yang localization card identifies a real obstruction: the arithmetic
infinite-volume point is the marginal Poisson point where an interior crystalline forcing theorem
does not act directly.  That kills the statement “zeta itself is a strict ferromagnet.”  It does not
kill approximation from the interior of a closed zero-location cone.

The present detour asks for finite source-defined ferromagnets first.  Their field-fugacity zeros
are on the unit circle by the Lee--Yang theorem.  A Cayley transform converts those circles into
real-rooted finite polynomials.  If the transformed partition polynomials converge locally
uniformly to `E Xi`, with `E` entire and zero-free, nonreal Xi zeros are impossible.  The arithmetic
point may be marginal in the limit; it need not carry a strict finite-volume interaction margin.

This is a constraint construction.  No thermodynamic flow or claim that heat evolution transports
zeta to the line is used.

## The closed chain

For each finite source aperture `P`, choose a finite spin graph `G_P=(V_P,E_P)` and couplings
`J_(P,e)>=0`, all determined from the Euler--Gamma/theta packet before inspecting any Xi zero.  With
one common field fugacity `z`, normalize the partition function as a polynomial

```text
Z_P(z) = sum_(sigma in {+1,-1}^V_P)
           exp(sum_(e={i,j}) J_(P,e) sigma_i sigma_j)
           z^(number of negative spins).
```

Then seek:

```text
finite Euler prime words and completed Gamma/theta boundary data
  -> squarefree support marker plus complete weighted boundary germ
       [PROVED IN LEAN]
  -> source cumulants at aperture P
  -> inverse ferromagnetic Ising realization J_(P,e)>=0
       [OPEN CORE A: source point lies in the ferromagnetic moment cone]
  -> Z_P has every fugacity zero on |z|=1
       [CLASSICAL LEE--YANG; TWO-SPIN BLOCK FORMALIZED]
  -> Cayley polynomial
       Q_P(w)=(w+i a_P)^deg(Z_P)
              Z_P((w-i a_P)/(w+i a_P))
     has only real finite zeros
  -> normalized local-uniform limit
       A_P Q_P(w) -> E(w) Xi(w), E entire and zero-free
       [OPEN CORE B: completed source comparison]
  -> E Xi has no nonreal zero
  -> Xi has no nonreal zero
  -> every nontrivial zeta zero has real centered coordinate
  -> RH.
```

Roots at fugacity `z=1`, which Cayley sends to infinity, must be removed or tracked by degree loss.
A constant phase normalization makes `Q_P` real.  Local-uniform convergence, not coefficientwise or
thermodynamic free-energy convergence, is the zero-preserving topology.

## Exact finite floor in Lean

The normalized two-spin interaction is

```text
L_c(z)=1+2cz+z^2,                 c=exp(-2J).
```

`LeeYangQuadraticBlock.lean` identifies it with the already formalized reciprocal quadratic block
and proves

```text
all zeros of L_c lie on |z|=1  <->  c^2<=1.
```

Hence the algebraic ferromagnetic chamber `0<=c<=1` forces the circle law.  The same file proves a
sharp no-go: `z^2 L_c(z^(-1))=L_c(z)` for every `c`, but at `c=2` circle localization fails.  Thus
functional-equation symmetry is not the finite engine; source-produced coupling inequalities are.

The result is the common quadratic floor of the Lee--Yang and Ihara detours, but the large chains
are different.  Ihara requires a source-constrained Ramanujan adjacency bound.  This route requires
a source-constrained ferromagnetic inverse problem and uses the global Lee--Yang theorem for the
full spin partition polynomial.

The first direct arithmetic construction is now closed in Lean.  Pairing one positive Euler weight
`a` with its reciprocal gives normalized coefficient

```text
c(a)=(a+a^(-1))/2 >= 1.
```

The resulting reciprocal block is Lee--Yang only at `a=1`; every contracting Euler weight
`0<a<1` produces an off-circle reciprocal pair.  Thus functional-equation pairing cannot be used
as the Ising interaction.  Arithmetic data must be converted into a true ferromagnetic coupling
`c=exp(-2J)<=1` or into another verified Lee--Yang measure.

## Source coordinates already available

`PrimeWordEnsembleBoundaryTomography.lean` proves that the complete normal boundary germ of any
finite integer-weighted word ensemble recovers every positive support-cardinality aggregate.
`PrimeSupportMultivariateLiftMarker.lean` retains the actual squarefree support set before that
aggregation.  These give a finite family of source cumulants without feeding in Xi zeros.

They do not imply ferromagnetism.  The inverse Ising map must place those cumulants in the
ferromagnetic moment cone, whose low faces satisfy positive association and Griffiths-type
inequalities.  This is the first substantive arithmetic test, not a technical afterthought.

## Hard attacks and positive successors

1. **Marginal-point attack.**  The strict infinite-volume Lee--Yang forcing degenerates at the
   arithmetic Poisson point; the prior card correctly rules out direct interior forcing.
   **Positive successor:** construct every finite approximant in the strict ferromagnetic chamber
   and use closure only at the locally uniform limit.  Boundary membership needs no uniform positive
   interaction margin.
2. **Reciprocity attack.**  Palindromic field polynomials may have reciprocal off-circle pairs.
   **Positive successor:** the exact two-spin coefficient selector is now formalized; at arbitrary
   volume use the full ferromagnetic Lee--Yang theorem, not reciprocity.
3. **Zero-feeding attack.**  Any real entire function can be approximated after choosing its desired
   zeros by suitable circle-rooted polynomials if enough freedom is allowed.
   **Positive successor:** `G_P`, its auxiliary spins, and every coupling must be a functor of the
   finite Euler--Gamma/theta packet.  Xi enters only in the later comparison theorem.
4. **Reciprocal-Euler construction attack.**  The obvious block
   `(1+a z)(1+a^(-1)z)` has coefficient `(a+a^(-1))/2>=1` and lies on the circle only at `a=1`;
   this is now formalized.
   **Positive successor:** encode arithmetic values as interaction energies with
   `exp(-2J)<=1`, not as reciprocal local fields.
5. **Signed-source attack.**  A pairwise ferromagnetic high-temperature expansion has nonnegative
   interaction weights, while completed source formulas contain cancellations.
   **Positive successor:** first test the actual connected source cumulants against the
   ferromagnetic moment cone.  If a low GKS/FKG inequality fails, direct pairwise Ising realization
   is retired.  The only live repair is a source-defined single-site or multispin measure with a
   separately proved Lee--Yang property; an arbitrary signed observable is not allowed.
6. **Gauge-frustration attack.**  Absorbing negative couplings by spin flips works only when the sign
   pattern is unfrustrated and may alter the common field variable.
   **Positive successor:** require an explicit gauge with all transformed interactions
   nonnegative and a uniform field, or record the frustrated cycle as a terminal obstruction.
7. **Coefficient-matching attack.**  Positive coefficients of `Z_P` cannot directly reproduce every
   signed Taylor coefficient of Xi.
   **Positive successor:** comparison is after the Cayley transform and zero-free Gamma
   normalization, where phases and alternating coefficients are permitted.  No direct equality of
   raw fugacity coefficients is required.
8. **Thermodynamic-limit attack.**  Convergence of pressure or free energy away from the zero set
   does not preserve the divisor.
   **Positive successor:** prove locally uniform convergence of the normalized entire partition
   functions on every compact centered-coordinate set, with a nonzero limit.
9. **Periodicity attack.**  Exponential field scaling produces vertically repeated zeros.
   **Positive successor:** use the rational Cayley transform at finite degree.  If microscopic
   exponential scaling is later needed, restrict to an expanding fundamental strip and prove the
   extra sheets escape every compact set.
10. **Trivial-factor attack.**  Decoupled auxiliary spins and field-independent normalizations can
   introduce zeros or degree artifacts.
   **Positive successor:** split every auxiliary factor explicitly and prove that the limiting
   residual `E` is entire and zero-free.
11. **Finite-moment attack.**  Matching a bounded number of correlations cannot determine a
    partition polynomial.
    **Positive successor:** use a triangular schedule in which aperture, interaction order, and
    retained source-cumulant depth grow together, with finite coefficient determination at every
    stage.

Every no-go leaves a positive object: the closed ferromagnetic moment cone, its frustrated-sign
obstruction class, or the zero-free relative factor.  A failure at low aperture therefore produces
a finite classification theorem rather than another metaphor.

## Concrete first theorem to test

At the smallest aperture supporting two distinct prime labels, compute the complete marked source
cumulants through order four.  Determine whether they are the correlations of a finite common-field
pairwise Ising model with all `J_e>=0`.  This is a finite semialgebraic inverse problem:

```text
source cumulant packet belongs to ferromagnetic Ising moment cone?
```

If yes, increase the aperture and seek a functorial graph extension.  If no, extract the first
violated positive-association inequality and formalize it as a source/ferromagnet obstruction; then
test the Lieb--Sokal/Newman single-site Lee--Yang extension rather than weakening the sign condition.

## Primary parent results

- T. D. Lee and C. N. Yang, *Statistical Theory of Equations of State and Phase Transitions. II.
  Lattice Gas and Ising Model*, <https://doi.org/10.1103/PhysRev.87.410>;
- C. M. Newman, *Zeros of the Partition Function for Generalized Ising Systems*,
  <https://doi.org/10.1002/cpa.3160270203>;
- E. H. Lieb and A. D. Sokal, *A General Lee--Yang Theorem for One-Component and Multicomponent
  Ferromagnets*, <https://doi.org/10.1007/BF01213009>.

These results provide the finite zero-location engine.  None supplies the arithmetic inverse-Ising
realization or the completed determinant comparison.

## Kill conditions

Retire pairwise Ising realization if the first exact completed source packet violates a necessary
ferromagnetic correlation inequality; retire every Ising version if no source-defined Lee--Yang
single-site measure survives that obstruction; retire the limit if the graphs or couplings are
chosen from Xi zeros, if comparison introduces a zero-bearing factor, if Cayley sheets do not escape
compact sets, or if convergence is weaker than locally uniform.

## Gates

- [x] old marginality no-go retained and converted to an interior-approximation target
- [x] exact two-spin coefficient/circle selector formalized
- [x] reciprocity-only failure formalized and converted to the coupling-inequality target
- [x] reciprocal pairing of contracting Euler weights formally excluded; interaction-energy target isolated
- [x] source-pure finite cumulant packet identified in formal Lean
- [x] two-ended Cayley/locally-uniform chain to RH stated
- [ ] smallest completed source packet tested against the ferromagnetic moment cone
- [ ] functorial finite ferromagnetic realization constructed at every aperture
- [ ] full-volume Lee--Yang theorem imported or formalized for the chosen model class
- [ ] Cayley-normalized local-uniform comparison with zero-free factor times Xi
- [ ] RH capstone formalized
