# Prime-source ferromagnets, Lee--Yang closure, and RH

- **ID:** `prime-source-ferromagnetic-ising-lee-yang-limit-rh`
- **Stage:** 1-in-progress
- **Type:** `[LARGE OUTLANDISH DETOUR] [CONJECTURE] [FORMALIZED FINITE CONSUMER]`
- **Lean inputs:** `formal/GaloisForLFunctions/RHTower/LeeYangQuadraticBlock.lean`,
  `formal/GaloisForLFunctions/RHTower/EulerReciprocalLeeYangNoGo.lean`,
  `formal/GaloisForLFunctions/RHTower/PrimeLeeYangPolydisk.lean`,
  `formal/GaloisForLFunctions/RHTower/PrimeEulerLeeYangAmplitudeNoGo.lean`,
  `formal/GaloisForLFunctions/RHTower/PrimeEulerFerromagneticInteraction.lean`,
  `formal/GaloisForLFunctions/RHTower/TwoSpinFKGLeeYangBridge.lean`,
  `formal/GaloisForLFunctions/RHTower/PrimeIsingTreeCavity.lean`,
  `formal/GaloisForLFunctions/RHTower/IsingCavityRapidityAudioCascade.lean`,
  `formal/GaloisForLFunctions/RHTower/PrimeIsingTreeFKExpansion.lean`,
  `formal/GaloisForLFunctions/RHTower/PrimeWordEnsembleBoundaryTomography.lean`,
  `formal/GaloisForLFunctions/RHTower/PrimeSupportMultivariateLiftMarker.lean`, and
  `formal/GaloisForLFunctions/XiLaguerrePolya.lean`
- **Prior no-go:** `../0-backlog/lee-yang-localization.md`
- **Statement:** `[CONJECTURE]` A cofinal family of finite multivariate ferromagnetic partition
  functions, constructed functorially from the completed prime source and evaluated at the
  inhomogeneous fields `z_p(z)=exp(-log(p) I z)`, converges locally uniformly to a zero-free entire
  factor times `XiC`.  The multivariate Lee--Yang theorem makes every finite approximant zero-free
  off the real centered axis, so the limit forces RH.

## Goal and the positive repair of the old marginality theorem

The earlier Lee--Yang localization card identifies a real obstruction: the arithmetic
infinite-volume point is the marginal Poisson point where an interior crystalline forcing theorem
does not act directly.  That kills the statement “zeta itself is a strict ferromagnet.”  It does not
kill approximation from the interior of a closed zero-location cone.

The present detour asks for finite source-defined ferromagnets first.  Give each prime site its own
field

```text
z_p(z)=exp(-log(p) I z),       XiC(z)=xi(1/2+I z).
```

Lean proves the exact geometry

```text
|z_p(z)|<1  <-> Im z<0,
|z_p(z)|=1  <-> Im z=0,
|z_p(z)|>1  <-> Im z>0.                                  (1)
```

Thus the real centered axis is the common prime unit torus, not merely the image of one artificial
common fugacity.  Multivariate Lee--Yang nonvanishing in the open polydisk and its common exterior
then makes each evaluated finite partition function zero-free on both nonreal half-planes.  A
locally uniform nonzero limit `E XiC`, with `E` entire and zero-free, has the same property by
Hurwitz.  The arithmetic point may be marginal in the limit; it need not carry a strict
finite-volume interaction margin.

This is a constraint construction.  No thermodynamic flow or claim that heat evolution transports
zeta to the line is used.

## The closed chain

For each finite source aperture `P`, choose a finite spin graph `G_P=(V_P,E_P)`, a map from its
distinguished sites to primes, and couplings `J_(P,e)>=0`, all determined from the Euler--Gamma/theta
packet before inspecting any Xi zero.  Normalize its multiaffine field partition function as

```text
Z_P((u_v)) = sum_(sigma in {+1,-1}^V_P)
               exp(sum_(e={i,j}) J_(P,e) sigma_i sigma_j)
               product_(v: sigma_v=-1) u_v.
```

Then seek:

```text
finite Euler prime words and completed Gamma/theta boundary data
  -> squarefree support marker plus complete weighted boundary germ
       [PROVED IN LEAN]
  -> prime-labelled source cumulants at aperture P
  -> inverse multivariate ferromagnetic realization J_(P,e)>=0
       [OPEN CORE A: source point lies in the ferromagnetic moment cone]
  -> Z_P((u_v)) != 0 whenever all |u_v|<1 or all |u_v|>1
       [CLASSICAL MULTIVARIATE LEE--YANG]
  -> F_P(z)=A_P(z) Z_P((z_(p(v))(z))) has no nonreal zero
       [PRIME POLYDISK GEOMETRY PROVED IN LEAN]
  -> F_P -> E XiC locally uniformly on C, with E entire and zero-free
       [OPEN CORE B: completed source comparison]
  -> E XiC has no nonreal zero by Hurwitz
  -> XiC has no nonreal zero
  -> every nontrivial zeta zero has real centered coordinate
  -> RH.
```

Here `A_P` is a source-defined entire normalization which must itself be zero-free.  Local-uniform
convergence, not coefficientwise or thermodynamic free-energy convergence, is the zero-preserving
topology.  A common-fugacity Cayley transform remains a secondary finite model, but it is no longer
needed for the main closure.

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

The multivariate prime-field selector is also formalized.  For every prime `p`,
`PrimeLeeYangPolydisk.lean` proves `(1)`.  As a zero-interaction baseline it defines

```text
F_P(z)=product_(p in P) (1+exp(-log(p) I z))
```

and proves directly that every zero of `F_P` has `Im z=0`.  Hence incommensurable prime periods do
not obstruct finite Lee--Yang localization: the common torus is the entire real centered axis and
the upper and lower half-planes are the common exterior and interior.  This baseline does not
approximate `XiC`; it isolates the actual new theorem as a completed-source interacting limit.

The physical Euler amplitude is a separate obstruction.  The actual local monomial is

```text
p^(-1/2) exp(-log(p) I z).
```

`PrimeEulerLeeYangAmplitudeNoGo.lean` proves that its norm is

```text
exp(log(p)(Im z-1/2)),
```

so it is strictly inside the disk on `Im z=0` and reaches the unit circle only at `Im z=1/2`, the
strip boundary `Re s=0`.  Therefore raw Euler monomials cannot be used as the Lee--Yang fields.
The square-root amplitudes must be absorbed into true spin interactions or a separately zero-free
completed normalization while the centered characters remain the field variables.

The first positive conversion is now formalized.  The same amplitude

```text
c_p=p^(-1/2)=exp(-log(p)/2)
```

lies in the ferromagnetic chamber `0<c_p<=1`.  Keeping `u_p(z)` as the field and using `c_p` as the
two-spin coefficient gives

```text
L_p(z)=1+2c_p u_p(z)+u_p(z)^2.
```

`PrimeEulerFerromagneticInteraction.lean` proves that every zero of `L_p`, and every zero of an
arbitrary finite product of these prime blocks, has `Im z=0`.  The construction uses only prime
weights and closes both finite ends of the Lee--Yang chain.  It is not yet the completed Euler
factor: reciprocal Euler pairing has coefficient `c_p+c_p^(-1)` instead of `2c_p`.  That explicit
coefficient defect is now the local source-comparison target.

The first ferromagnetic moment-cone face is now source-facing in Lean.  For any symmetric two-site
packet with aligned weight `A>0` and disagreement weight `B`,

```text
Z_(A,B)(z)=A+2Bz+Az^2,
Delta_FKG(A,B)=A^2-B^2,
```

`TwoSpinFKGLeeYangBridge.lean` proves

```text
every zero of Z_(A,B) lies on |z|=1  <->  Delta_FKG(A,B)>=0.
```

After normalization, the same inequality is exactly the existing Ihara spectral bound at
`(q,lambda)=(1,-2B/A)`.  The prime square-root packet satisfies this face strictly.  Reciprocal
Euler pairing has the exact defect

```text
Delta_FKG(1,(a+a^(-1))/2)=-(a^2-1)^2/(4a^2),
```

and violates it strictly for `0<a<1`.  This discharges the two-site determinant check for the
source-native prime interaction and turns the same check into a reusable hypothesis for any
unnormalized completed source packet.  It does not establish positivity of every packet weight or
membership of the higher completed packet in the full ferromagnetic moment cone.

The finite-volume theorem is now internal for the tree model class.  The exact rooted-tree cavity
update

```text
T_c(r)=(c+r)/(1+cr)
```

is the `HTGeometry.CayleySchur` Blaschke factor with node `-c`, and satisfies

```text
normSq(1+cr)-normSq(c+r)=(1-c^2)(1-normSq(r)).
```

`PrimeIsingTreeCavity.lean` formalizes arbitrary finite rooted prime-labelled trees with any finite
branching and edge weights `0<=c_e<=1`.  It proves open-polydisk nonvanishing by the cavity ratio,
the exact global spin-inversion law

```text
Z_T(u)=(product_(v in T) u_v) Z_T(u^(-1)),
```

and therefore `Im z=0` for every zero after substituting the centered prime fields.  This is a
genuinely interacting finite class, not a product theorem.  The same module proves that the
one-edge common-field tree is the existing `leeYangPairBlock`, that the prime-Euler one-edge tree is
the existing `primeEulerFerromagneticBlock`, and that zero-disagreement duplicate-free chains are
the existing synchronized prime clusters.  At the other endpoint, `c=1` is zero physical
interaction and duplicate-free chains are exactly the existing independent prime partition.  Thus
one formal tree class contains both old endpoints and the interacting interior.

Every finite tree partition is also proved entire.  Applying the existing locally uniform
zero-transfer theorem gives the route-facing capstone

```text
T_n finite prime Ising trees,
E entire and nowhere zero,
Z_(T_n) -> E XiC locally uniformly
----------------------------------
RH.
```

Consequently all generic analytic and finite zero-location hypotheses have been discharged.  The
remaining source problem is exactly to realize the completed packets by a cofinal compatible tree
family and prove this locally uniform comparison, or to extract the first obstruction to doing so.

Audio scattering and special-relativistic rapidity supply a further exact simplification.  The
cavity maps form the Möbius cascade

```text
T_c(T_d(r))=T_((c+d)/(1+cd))(r),       |r|<1,
```

so serial sections collapse to one effective ferromagnetic coupling.  At the centered origin all
prime fields equal one, and `IsingCavityRapidityAudioCascade.lean` proves for every finite tree

```text
Z_T(0)=2 product_(e in T) (1+c_e) != 0.
```

The module packages this as `centralNormalizedPrimeIsingTreePartition`, proves its value at zero is
one without changing any zero, and supplies a locally uniform normalized-tree capstone to RH.  The
comparison problem can therefore impose unit central normalization canonically rather than carry
an arbitrary nonzero scalar at each aperture.

The Fortuin--Kasteleyn deletion--contraction expansion is now internal as well.  For every edge,

```text
(a+c b, c a+b) = c(a+b,a+b) + (1-c)(a,b).
```

`PrimeIsingTreeFKExpansion.lean` enumerates every cut/synchronized bond configuration of an
arbitrary finite tree and proves

```text
Z_T(u) = sum_(bond configurations B) w_B Z_B(u),
w_B >= 0,                 sum_B w_B = 1.
```

It further proves that every fixed `Z_B` factors exactly into the two-state synchronized partition
blocks of its connected components.  Thus the tree class is a convex cone over the existing
`synchronizedPrimeClusterPartition` basis, with independent spins at the all-cut endpoint and the
fully synchronized cluster at the all-open endpoint.  Open Core A is correspondingly sharper:
the completed source packet must admit this nonnegative, product-compatible cluster coefficient
factorization.  A failed coefficient test now retires the entire tree-Ising subclass rather than
only one proposed graph.

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
5. **One-common-field attack.**  Assigning all primes one artificial fugacity discards their
   logarithmic scales and forces a later Cayley comparison.
   **Positive successor:** use the inhomogeneous fields `z_p(z)=exp(-log(p) I z)`.  Their exact
   common polydisk/torus/exterior geometry is proved in Lean and already gives a finite independent
   partition function whose zeros are all real in the centered coordinate.
6. **Physical-amplitude attack.**  The actual Euler monomial contains `p^(-1/2)`; its unit circle is
   the strip boundary, not the critical line.  Directly inserting it as a fugacity destroys the
   prime-torus selector.
   **Positive successor:** keep `exp(-log(p) I z)` as the field and derive the square-root weights
   from ferromagnetic interactions or a proved zero-free completed normalization.  The first option
   is now achieved finitely: `p^(-1/2)` is a ferromagnetic pair coefficient and gives critical-line
   prime blocks at every finite aperture.  Open Core A has narrowed to removal of the explicit
   reciprocal-pair coefficient defect and construction of the interacting completed limit.
7. **Signed-source attack.**  A pairwise ferromagnetic high-temperature expansion has nonnegative
   interaction weights, while completed source formulas contain cancellations.
   **Positive successor:** first test the actual connected source cumulants against the
   ferromagnetic moment cone.  If a low GKS/FKG inequality fails, direct pairwise Ising realization
   is retired.  The only live repair is a source-defined single-site or multispin measure with a
   separately proved Lee--Yang property; an arbitrary signed observable is not allowed.
8. **Gauge-frustration attack.**  Absorbing negative couplings by spin flips works only when the sign
   pattern is unfrustrated and may invert selected prime fields, destroying the all-inside or
   all-outside chamber.
   **Positive successor:** require an explicit gauge with all transformed interactions
   nonnegative which preserves the common prime-field chamber, or record the frustrated cycle or
   mixed-chamber inversion as a terminal obstruction.
9. **Coefficient-matching attack.**  Positive coefficients of `Z_P` cannot directly reproduce every
   signed Taylor coefficient of Xi.
   **Positive successor:** comparison occurs after substituting the complex prime fields and a
   zero-free Gamma normalization, where phases and alternating centered Taylor coefficients are
   permitted.  No direct equality of raw fugacity coefficients is required.
10. **Thermodynamic-limit attack.**  Convergence of pressure or free energy away from the zero set
   does not preserve the divisor.
   **Positive successor:** prove locally uniform convergence of the normalized entire partition
   functions on every compact centered-coordinate set, with a nonzero limit.
11. **Periodicity attack.**  Each single prime activity is periodic on the real axis, but distinct
    prime periods are incommensurable and finite interacting exponential polynomials need not have
    a common nonzero period.
    **Positive successor:** no periodicity is assumed in the closure.  Prove local-uniform
    convergence directly on compact subsets of the centered plane; any residual common period of a
    proposed approximant family is a falsifying obstruction unless it escapes with the aperture.
12. **Trivial-factor attack.**  Decoupled auxiliary spins and field-independent normalizations can
   introduce zeros or degree artifacts.
   **Positive successor:** split every auxiliary factor explicitly and prove that the limiting
   residual `E` is entire and zero-free.
13. **Finite-moment attack.**  Matching a bounded number of correlations cannot determine a
    partition polynomial.
    **Positive successor:** use a triangular schedule in which aperture, interaction order, and
    retained source-cumulant depth grow together, with finite coefficient determination at every
    stage.

Every no-go leaves a positive object: the closed ferromagnetic moment cone, its frustrated-sign
obstruction class, or the zero-free relative factor.  A failure at low aperture therefore produces
a finite classification theorem rather than another metaphor.

## Concrete first theorem to test

At the smallest aperture supporting two distinct prime labels, compute the complete marked source
cumulants through order four.  Determine whether they are the correlations of a finite
prime-labelled pairwise Ising model with all `J_e>=0`.  This is a finite semialgebraic inverse
problem:

```text
source cumulant packet belongs to ferromagnetic Ising moment cone?
```

If yes, increase the aperture and seek a functorial graph extension.  If no, extract the first
violated positive-association inequality and formalize it as a source/ferromagnet obstruction; then
test the Lieb--Sokal/Newman single-site Lee--Yang extension rather than weakening the sign condition.

## Primary parent results

- T. D. Lee and C. N. Yang, *Statistical Theory of Equations of State and Phase Transitions. II.
  Lattice Gas and Ising Model*, <https://doi.org/10.1103/PhysRev.87.410>;
- H. A. Bethe, *Statistical Theory of Superlattices*,
  <https://doi.org/10.1098/rspa.1935.0122>;
- K. de'Bell and M. L. Glasser, *The Ising model on a closed Cayley tree: Zeros of the partition
  function*, <https://doi.org/10.1016/0375-9601(84)90063-X>;
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
chosen from Xi zeros, if comparison introduces a zero-bearing factor, if a gauge produces a mixed
inside/outside prime-field chamber, if a nonzero common period persists on compact sets, or if
convergence is weaker than locally uniform.

## Gates

- [x] old marginality no-go retained and converted to an interior-approximation target
- [x] exact two-spin coefficient/circle selector formalized
- [x] reciprocity-only failure formalized and converted to the coupling-inequality target
- [x] reciprocal pairing of contracting Euler weights formally excluded; interaction-energy target isolated
- [x] exact prime polydisk/critical-torus/exterior geometry formalized
- [x] finite independent prime-spin partition proved zero-free off the centered real axis
- [x] physical Euler square-root amplitude displacement formally excluded
- [x] two-site FKG determinant made equivalent to the Lee--Yang and Ihara selectors
- [x] prime interaction shown to satisfy the FKG face strictly; reciprocal Euler pairing shown to violate it strictly
- [x] source-pure finite cumulant packet identified in formal Lean
- [x] two-ended multivariate Lee--Yang/locally-uniform chain to RH stated
- [ ] smallest completed source packet tested against the ferromagnetic moment cone
- [ ] functorial finite ferromagnetic realization constructed at every aperture
- [x] full-volume Lee--Yang theorem formalized for arbitrary finite rooted tree models
- [x] serial cavity sections collapsed and canonical nonzero central normalization formalized
- [x] arbitrary tree partitions decomposed as convex FK mixtures of synchronized cluster products
- [ ] prime-field local-uniform comparison with zero-free factor times `XiC`
- [x] RH capstone formalized from the tree comparison with a zero-free entire factor
