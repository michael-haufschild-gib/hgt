# CHMD: exact cardinal packets in the literal arithmetic graph

Status: FORMALIZED. Dependency-closed paper proof, five leaf builds, and all final audits passed. Overall goal remains unconditional RH.

## Obstacle and structural target

The completed graph now contains every admissible finite theta-divisor source and has its exact signed zero pairing. Existing `CHMDExactDivisorPackets` cardinal functions use a rational pole filter with singularities at +/-3i. Their strip admissibility does not prove admission to the literal source graph. Close this gap by constructing genuinely theta-relative cardinal sources with a polynomial polar notch, full analytic multiplicity removed, and exact finite zero-orbit pairings.

## Paper construction

For a Xi zero a with Re(a)>0, let m=ord_a Xi and L consist of m copies of a. The actual source with transform H(z)=Xi(z)/P_L(z) is smooth, theta dominated, and admitted to the full graph. Both H and P_L are entire; the equality of orders at a forces H(a)!=0. The polynomial notch e(X)=X+1/4 has degree 1<=m. Its realized source has transform J(z)=H(z)(z^2+1/4), nonzero at a, zero at both polar points, and zero at every Xi zero outside {a,-a}. Divide the source by J(a). Its transform takes exactly the value 1 on {a,-a}, and 0 at every other Xi zero. No simplicity or RH assumption is used.

Real and imaginary parts yield real graph vectors with exactly prescribed conjugate-orbit values. At a real orbit the real packet is visible and has positive complete signed energy. At a nonreal orbit the real and imaginary packets separate the positive and negative directions, with all multiplicity weights and both polar terms preserved. Establish the exact identities before making any sign claim.

## Exact signed form and primitive admission

Write A(z)=1 when z is a or -a, and 0 otherwise; B(z)=A(conjugate z). For c in C, the actual real source Re(c u) has paper Fourier value V_c(z)=(c A(z)+conjugate(c) B(z))/2 at every Xi zero. Its values at both polar points vanish. Conjugation gives V_c(conjugate z)=conjugate(V_c(z)), so the full W summand is multiplicity times V_c(z)^2. Its real part is

  Re(c)^2 ((A+B)/2)^2 - Im(c)^2 ((A-B)/2)^2.

The carrier-to-gamma map is injective. These summands vanish outside the finite four-point orbit, so their sums are genuinely summable. Define K+ and K- by summing the two displayed squares with the original positive multiplicities. Then E(Re(c u))=Re(c)^2 K+ - Im(c)^2 K-. Every Xi zero corresponds to an actual zeta carrier point; its positive multiplicity makes K+ strictly positive. When Im(a)!=0 and Re(a)>0, A and B have disjoint support; K+=K-. When Im(a)=0, A=B and K-=0.

The regularity theorem supplies full graph vectors p=Re(u), q=Im(u), with their inverse-Doob source coordinates and strong compact-test approximations. Apply the exact signed identity at c=1, -i, and 1-i; polarization gives B(p,q)=0. Thus

  E(r p+s q)=r^2 K+ - s^2 K-.

Ground pairing is -integral(f cosh(x/2)) for any literal admitted source f. For even compact sources this equals -Re FT_f(i/2). Strong bulk graph convergence and unconditional polar Fourier convergence extend the identity to the theta-relative decay class. Consequently both p and q, and every real combination, are orthogonal to the theta ground state. For a nonreal orbit the exact form is K+(r^2-s^2), K+>0; pairing any putative zero combination against p and q forces r=s=0. This is a genuine primitive signed plane in the original full arithmetic graph.

Hardy's existing unconditional positive real Xi zero gives an unconditional primitive cardinal frame with positive real-vector energy and transform equal to 1 at its center. No nonreal zero is asserted to exist.

This is the missing admission step for exact finite spectral interpolation, rather than a new positivity receiver. Continuous evaluation representers on the entire completed graph remain a later target; even packets initially detect the even sector.

## Corpus evidence

- `ThetaZeroDivisionRealization`: actual sources, full list factorization, multiplicity count of `listDivisor`, smooth seams, real-part transform.
- `ThetaEndpointDivisorClassification`: finite Xi orders, `xiZeroMult`, positivity of real part after choosing sign, replicate divisor formulas.
- `CHMDFiniteDivisorPairing`: discharged regularity/domain and exact signed graph identity.
- `CHMDExactDivisorPackets`: full-multiplicity abstract cardinal functions and orbit algebra; its rational filter is not reused for physical admission.

Two deep corpus searches completed, nonpartial with unavailable semantic-coverage warning. Relevant claims were located directly in Lean; generic retrieved pairing candidates were inapplicable.

## Work plan

1. Prove full-multiplicity replicated division has a nonzero terminal value.
2. Construct normalized polar-free cardinal sources and prove exact zero-set interpolation.
3. Realize actual graph vectors and derive orbit pairing/sign identities, including an unconditional nonzero instance.
4. Leaf builds, plain direct Lean audits, API/axiom checks, umbrella wiring, index/lint, cleanup.

Steps 1-4 complete. Five leaf builds passed with no own warnings; all five leaves are wired exactly once. Final plain `lake env lean <leaf>` audits passed sequentially for all five leaves, each with an empty log. All 67 new declarations passed axiom inspection with only `propext`, `Classical.choice`, and `Quot.sound`; 113 explicit mathlib `have := @Name` probes passed. Formal lint passed, with existing large-file warnings. No full build or umbrella build was run.

## Formal artifacts

- `ThetaDivisorCardinalSource`: full analytic multiplicity, nonvanishing normalization, polynomial notch, regularity, exact cardinal values, both polar cancellations.
- `ThetaCardinalOrbitReadout`: convention bridge, real-packet orbit readout, finite support and actual summability.
- `CHMDCardinalOrbitEnergy`: exact signed two-coordinate energy, positive/negative masses, balance for nonreal orbits and vanishing negative mass on real orbits.
- `CHMDPolarGraphMoments`: literal ground pairing, compact polar identity, strong graph passage, primitive admission.
- `CHMDCardinalGraphGeometry`: actual carrier correspondence, strictly positive orbit mass, primitive graph frames, exact form, nonreal independence, unconditional positive real instance.

Total: 742 lines, 67 explicit declarations, no raised heartbeat limits. Main existence theorem: `CHMDDoobGraph.exists_cardinalGraphFrame`. Premise-free nonzero theorem: `CHMDDoobGraph.exists_positive_primitive_cardinal_frame`.

## Boundary

No claim of primitive positivity, completeness of the cardinal family, exclusion of nonreal zeros, or RH. Concurrent Klein-Gordon and Meyer-flow work remains outside this write scope.

Next structural question: extend the exact cardinal readouts to continuous signed evaluation representers against arbitrary vectors of the completed graph, then identify the actual radical. Even packets alone do not settle the odd sector or justify a complete spectral expansion. The present construction removes the domain/admission gap; it does not assume or prove that this spectral family spans the primitive space.
